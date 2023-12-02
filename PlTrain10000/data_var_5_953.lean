variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330878011249940342933448588042 : (True → (p3 → ((True ∨ p3) → (p4 ∨ (((True ∧ (p2 ∨ False)) ∧ p5) ∨ (((False ∨ p5) ∧ (p1 ∨ (p1 ∧ ((p5 ∨ True) → p2)))) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231563610352059426591207067250 : (((p5 → p2) ∨ p2) → (((((p5 → False) ∨ ((p3 ∧ p4) ∨ ((p2 ∧ False) → p1))) ∨ (((p3 ∧ p3) ∧ p3) → p2)) ∨ p2) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694251107498412800005574953398 : ((((((p4 ∨ (True → p1)) → p4) → (p3 ∧ ((p2 ∧ p4) ∧ (p4 ∨ p3)))) ∨ (((p3 ∨ (p4 → p5)) → (p3 ∧ (p4 ∨ False))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47111121781364327756701645951 : ((((((p3 ∧ True) → (p2 → (((p2 ∧ p1) ∨ (p4 → (p1 ∨ True))) ∧ (p1 → p5)))) ∨ p3) ∨ (p5 ∧ (p5 ∧ False))) ∨ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119929311496378912754699460814 : ((((p1 ∧ (p3 ∨ (((p5 ∨ (p1 ∨ ((p2 → p1) → p5))) → False) ∧ ((p2 → p5) ∧ p5)))) ∧ ((False ∧ p5) ∨ p4)) ∧ p4) → (p3 ∨ False)) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h21 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h22 : (p5 ∨ (p1 ∨ ((p2 → p1) → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h23 := h14 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345595302429203038913818893829 : (p3 → (((p3 → p3) ∧ (((p4 ∧ ((p2 ∧ ((True → p4) ∧ p3)) ∨ True)) ∧ (((p1 ∧ p1) ∧ p3) ∧ ((p2 ∧ p4) ∨ False))) ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135736566740384942960219667664 : ((((p1 ∧ (True ∨ ((True ∧ ((True ∧ p3) ∨ p5)) ∨ p2))) ∧ (p3 ∨ p5)) ∨ ((p5 → p3) ∨ ((p5 ∧ p2) ∨ True))) ∨ ((True ∧ p4) ∧ False)) := by
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
theorem thm_5_vars_152987139720662911977716417915 : ((p1 ∧ ((p1 → p5) ∧ ((p3 ∨ (True ∧ p5)) ∨ (p3 ∨ (((p1 ∨ p3) → (False ∨ p1)) → (p2 ∨ p4)))))) → ((p5 → (p4 ∧ p2)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h9
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : p5 := by
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h24 := h5 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h22
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : p5 := by
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h29 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h30 := h5 h29
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h31 := h2 h28
      -- We need to get the left conjuct of h31 based on <expert-advice>.
      let h32 := h31.left
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184906816919076538661306159353 : ((((p1 ∨ p3) ∨ p5) ∨ (((False ∨ p4) ∨ (p3 ∨ False)) → False)) ∨ (((p5 ∨ (True ∨ False)) ∨ ((p1 ∨ p2) ∧ p1)) ∨ ((p5 ∨ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_246582567216539006769148522472 : ((p5 ∧ p2) ∨ ((((p3 ∧ (p2 → p1)) ∧ (p5 ∨ p4)) ∨ p3) → (((p1 → p4) ∧ ((True ∨ (((p3 → p3) ∨ p3) ∨ False)) → False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ (((p3 → p3) ∨ p3) ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ (((p3 → p3) ∨ p3) ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117214313509241369391248456282 : ((True ∧ (((p3 ∧ p4) → p1) ∧ (p5 → (p3 → ((((p3 → p5) ∨ p5) → p1) → ((p4 ∨ p5) → ((True → True) → p2))))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55896588696557621325293610161 : (((p3 ∨ ((False ∨ p3) ∨ p3)) ∧ (((p3 ∨ (p3 ∧ ((True ∨ (False ∨ ((p3 → (p5 ∨ p5)) ∨ p1))) → p2))) ∨ (p2 → True)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864502967424447097834447223913 : ((((((p1 → ((p5 → False) → (p5 → p5))) ∧ p2) ∨ (((p2 → (p4 ∨ p3)) ∨ ((p5 → False) ∧ (p3 ∧ (p5 → p5)))) ∨ True)) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → ((p5 → False) → (p5 → p5))) ∧ p2) ∨ (((p2 → (p4 ∨ p3)) ∨ ((p5 → False) ∧ (p3 ∧ (p5 → p5)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226003973674595693717601035624 : (((p4 ∧ False) ∨ p4) ∨ (((((p4 → (p3 ∨ (p5 → p5))) → p4) → ((p1 ∨ p1) ∨ ((p4 ∧ p2) ∨ (p3 ∨ p5)))) ∨ p3) → (p5 ∨ True))) := by
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
theorem thm_5_vars_57639576746085545868516181027 : ((((p5 ∧ p4) ∨ p5) → ((p5 ∧ (p5 → ((True ∨ (False → (p3 ∨ p4))) → ((((p4 ∧ True) ∧ True) ∧ True) ∧ (p3 ∨ False))))) ∨ True)) ∨ p5) := by
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
theorem thm_5_vars_46453802561591823939606545074 : ((((p4 ∧ ((p3 ∨ p4) ∧ p4)) ∨ (((True ∨ (((p5 → (False ∧ (p4 → (False ∧ False)))) → p2) ∧ p3)) → True) → p5)) ∧ (p3 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103044141471975236868491087775 : ((((p1 ∨ ((p1 ∧ (p3 ∧ p2)) ∧ p1)) ∧ (((False ∧ (False ∧ (p5 → (True ∨ p5)))) ∧ (p4 ∧ True)) ∧ (False ∧ p3))) ∨ True) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257308475195743473257074840864 : ((p2 ∨ p4) → (((False ∧ False) ∨ (((p1 → True) ∧ (False ∨ p3)) ∨ ((((False ∧ (p2 → p5)) ∧ (p5 ∧ False)) → (p3 ∨ p5)) ∧ p3))) ∨ True)) := by
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
theorem thm_5_vars_652872180326212947299195801385 : ((((p4 ∨ (((True ∨ (False → False)) → (p5 ∨ (((False → p5) ∧ (p1 ∨ (p4 → p4))) → ((p4 ∨ p5) ∧ p2)))) ∧ p2)) ∧ (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200038741367216632570764731393 : (((p5 ∧ ((p3 → False) ∨ p5)) → (False ∧ p4)) → ((((p3 ∧ (p5 → (p3 ∨ (p4 ∧ p4)))) → (p2 → ((p2 → p5) → p1))) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∧ ((p3 → False) ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136095511929710924394223038512 : ((((p1 ∧ (((p1 ∧ p2) → p3) → p4)) ∨ p1) ∨ (((p2 → p2) ∨ (p3 → ((p2 → p3) ∧ (p5 ∨ p4)))) ∨ p5)) ∨ ((True ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645065534562372705224604638085 : ((((p3 ∨ ((p1 ∧ ((p5 ∨ p3) ∧ ((p3 ∧ ((p2 ∧ p1) ∧ ((p4 ∧ False) ∧ (p1 → p5)))) → ((p5 → p3) ∧ p2)))) ∨ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816904489711603286129624156739 : ((((((p1 → (p4 ∧ p1)) → (((p4 → False) ∨ ((p1 ∧ p3) → p2)) ∨ (((p4 ∧ (False ∧ (p2 ∧ p4))) → p4) → True))) → False) ∧ p1) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → (p4 ∧ p1)) → (((p4 → False) ∨ ((p1 ∧ p3) → p2)) ∨ (((p4 ∧ (False ∧ (p2 ∧ p4))) → p4) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589766055231889607261613137267 : (((((((p1 ∨ False) ∧ ((False ∨ ((p4 → (True → (p5 ∨ (p3 ∨ (p5 → False))))) → (False ∧ p4))) ∧ p4)) ∨ (False ∧ p4)) → False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205206131702358525733025822798 : (((p3 → (p5 ∨ False)) ∧ (p3 ∨ p4)) ∨ (((p2 ∧ (True ∧ False)) ∧ ((p1 → p5) ∨ (p1 ∨ (p5 ∧ (p5 → (True ∧ (False ∨ p4))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37088052806603699515041994756 : ((((((False ∧ p1) ∧ (((p5 → ((((p3 → False) ∧ p5) ∧ p4) → (p5 → (p4 → (p4 ∧ p1))))) ∧ p2) ∧ p1)) ∨ p2) ∧ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257808431101728733266990753517 : ((p3 ∨ p5) → ((((((p2 → True) → p4) → (p1 ∧ p5)) → ((False ∧ (p2 ∨ False)) ∧ ((p1 ∨ p5) ∨ p3))) ∨ p1) → (p5 ∨ (p1 ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338127085830957375566745051462 : (p1 → ((((p1 → (False → p1)) ∨ (p1 → p1)) → False) ∨ (True ∨ ((((p3 ∧ p5) ∨ True) ∧ ((False → (p3 → True)) ∨ (False → p4))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263896320402993542058986447184 : (True ∧ (((p5 → (p3 → False)) ∧ (((False → (p4 ∧ (True → p2))) → p3) ∧ False)) ∨ (p2 ∨ ((p3 ∨ False) → (p3 → (p5 ∨ (False → p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320127758892233264630865571630 : (p4 ∨ ((p4 ∨ (p2 ∧ p2)) → (p2 ∨ ((p4 → ((p5 ∧ (p3 ∨ p2)) ∨ ((False ∧ ((p2 ∧ (p4 ∧ (p1 ∨ p3))) ∧ p4)) ∧ p2))) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52593814630931286759181308360 : ((((p1 → ((p4 → p2) ∨ ((True ∨ p4) → p3))) → (p2 ∧ (True → p3))) ∨ (((p4 ∨ p4) ∧ ((False ∨ (p3 ∨ p5)) → False)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53680956286904547609490536495 : (((False ∧ (((False ∨ ((p2 ∨ p5) ∨ p5)) → False) → p2)) ∧ (p1 ∧ (((p4 ∧ (p5 → True)) → (True → ((p3 ∧ p2) ∧ True))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231714763838353710274622770877 : (((p2 ∧ p1) → p1) → (((p4 ∧ ((p2 ∨ (p2 ∧ (p1 ∨ True))) ∨ p3)) ∨ (p1 ∨ True)) ∨ (p2 → (True → (p1 ∨ ((p4 ∨ p1) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593124405477033396038907161320 : ((((((((False ∨ (True ∨ p1)) → (p1 → ((p3 ∧ p3) ∧ p4))) ∨ p1) ∧ ((False ∧ (p4 ∨ p1)) ∨ p5)) ∨ (p2 ∧ (True ∧ p2))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618194869538539565944147869897 : (((((((p3 ∨ p1) ∨ p5) ∧ p4) ∨ (((p1 → p2) ∨ p5) → ((p3 ∧ ((False ∧ (p5 ∨ (p2 → p3))) → (p2 → p5))) ∨ False))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341025241213099021135721774883 : (p2 → ((p4 ∧ ((p4 → ((p1 → (False → ((p1 ∧ ((p3 ∧ True) → p3)) ∨ True))) → ((p5 → p1) → (p5 ∧ (p2 ∧ p2))))) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37565490751333061385227070661 : ((((p4 ∨ ((((p1 ∧ (p5 → p1)) ∨ ((p3 ∨ p1) ∧ p5)) → ((p1 ∨ p4) → p1)) ∨ (p1 ∧ ((True ∧ p2) ∨ p3)))) ∨ True) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262293876820495355384897222250 : (True ∧ (((p4 → (p2 → (((p3 → True) → ((p5 ∨ True) ∨ (p3 → p1))) ∨ p4))) ∧ ((((p4 → (p2 ∨ False)) ∨ p2) ∨ p3) ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135236016698432847909033515490 : ((((p2 ∧ (p2 ∧ (p2 → p2))) → (p2 ∨ ((((p3 → p1) ∧ (p5 → (True ∨ p2))) → p2) ∨ False))) → (False ∨ p4)) ∨ (p5 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261223555698729542072248500463 : ((p4 → p5) → (((False → p3) → p4) ∨ ((True ∨ ((p5 ∨ (((True → p1) → (True ∨ (p4 → False))) → p3)) ∨ (True ∨ p1))) ∨ (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42805896415505638800554579019 : (((p1 → (((((((p4 → p1) ∧ p3) → (p4 → False)) ∧ (p1 → (p2 → False))) → p3) → (((False ∨ False) ∨ p5) ∨ False)) ∨ True)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44028726425676534728617218480 : (((((p4 ∨ p5) ∧ (p2 ∧ (((((True ∨ p4) → p2) ∨ p4) → (((p3 ∨ True) ∧ p1) ∨ p1)) ∨ (p1 ∧ p4)))) → (False → False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55003401163160115063564895106 : ((((p2 ∧ p3) → (p5 → (True → p1))) ∧ ((True ∧ False) ∨ ((True ∧ (p5 ∧ (((p5 → (p3 ∨ p2)) ∨ p1) ∨ True))) ∨ (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149893409176186766822622371126 : ((p2 ∨ (p1 ∧ ((p3 → ((p1 ∨ (p1 ∨ (p2 ∧ False))) ∧ (p2 ∧ (p2 ∨ ((p5 ∧ False) → p2))))) ∨ False))) ∨ (p1 → ((p1 → p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39695857375516096877550786400 : (((p4 ∨ (True ∧ ((p3 → ((((p2 ∧ p2) → ((p2 → p5) ∧ (((p1 ∨ p2) ∨ p4) ∧ p5))) ∧ p2) ∧ (p1 → p1))) ∨ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191737453684990287788012696709 : ((False ∨ (((p2 → p1) ∨ (p3 ∨ False)) ∧ (p2 → p4))) ∨ ((p4 → p1) ∨ ((p5 ∨ (True ∨ ((p3 → p3) ∨ p1))) ∨ (False ∧ (p1 → p3))))) := by
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
theorem thm_5_vars_38804010163238571843337328471 : (((((p1 ∧ (False → True)) ∧ p3) → ((False ∨ p5) ∨ (((p4 ∨ p4) ∧ (p3 ∨ p3)) → (p5 ∨ (p3 ∨ (False → (p2 ∨ p4))))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691472284566813905674197516103 : (((((p5 → True) ∨ ((p5 → (p5 ∨ True)) → ((p5 ∨ p1) ∨ (True → (True → p1))))) → ((p1 ∧ ((True ∧ p2) ∧ (p5 ∧ p2))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133964796170855374746353849678 : (((p4 → ((True → p1) → ((p2 ∨ ((False → ((p1 ∨ (p3 ∧ (p1 ∨ p1))) ∨ True)) ∧ (p1 ∨ p3))) → p5))) ∧ p1) ∨ ((p1 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37532773905918585685341662558 : ((((p2 ∧ (((((p3 ∨ p2) ∨ p2) ∧ p5) ∨ (p3 → p3)) → (True → (p1 ∨ ((p4 → (p3 → p1)) → (p5 ∧ True)))))) ∨ p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116285403381371439378824117678 : (((p2 ∨ (p2 ∨ False)) ∨ ((((True ∨ ((p2 ∨ True) ∧ p1)) ∧ p3) → (p4 ∧ ((p1 → p3) → (p3 ∧ False)))) ∨ (True ∧ True))) ∨ (p3 → p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258810124500520191362956378245 : ((True → False) → (p4 ∨ (((False → (True ∧ ((p5 → (p1 ∧ (p4 ∧ ((False ∧ (p4 → ((p4 → p3) → False))) ∨ p3)))) ∨ p2))) → p3) ∧ p2))) := by
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
theorem thm_5_vars_148793636465783246779671235771 : (((p1 → (p4 ∧ (p1 → (p5 ∨ p3)))) ∨ (((p5 ∨ p5) ∨ (False ∨ (False ∨ (True ∨ (True ∧ p3))))) ∨ p1)) ∨ ((p3 ∨ p4) → (p5 → False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172543425080631243360495919576 : ((((p2 → p5) ∧ p2) ∨ (p3 ∧ ((p1 ∧ ((p1 ∨ p1) ∧ p2)) ∧ (False ∨ p1)))) ∨ ((p5 → p4) ∨ ((False → (p1 ∨ True)) ∨ (False ∨ p3)))) := by
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
theorem thm_5_vars_308629243905610830246504987002 : (p2 ∨ (((p3 ∨ p2) → ((p1 ∨ ((p1 ∨ False) → (True ∨ (p1 ∧ (p3 ∨ p3))))) ∧ ((p2 ∨ ((p4 ∧ p2) ∨ p1)) ∧ (True ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251355322843660892100821614027 : ((p2 → p4) ∨ (((((p3 ∨ (True ∨ True)) → (((True ∧ (p4 ∨ p5)) ∧ p4) → ((p1 → False) → p3))) ∨ p3) ∨ (p1 → (p2 → p2))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650160249750256423190601653393 : (((((True ∧ ((p1 ∧ ((False → (p5 ∧ False)) ∨ (False → (p1 ∨ p5)))) ∧ (p2 ∨ p5))) ∧ ((False ∨ (p2 ∧ p1)) ∨ p5)) ∧ (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55183978732690178747561315669 : (((((True ∧ p2) ∨ (p3 ∨ p5)) → False) ∨ ((((p4 → p5) ∧ ((p5 → ((p2 ∨ p4) → ((False → False) ∧ p2))) → True)) → p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609422597788731535951279359845 : ((((((p1 → p5) → (((((p5 ∧ p1) ∧ (False → p1)) ∧ ((p4 ∨ (False ∧ ((p3 ∨ False) ∧ p1))) ∧ p2)) ∧ True) ∧ p3)) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_157640203438581106798347690352 : (((False ∨ ((p5 → (p3 ∨ (False → p3))) → (p1 ∧ (True ∧ (False → p3))))) ∧ ((False ∧ p1) ∨ p2)) ∨ (((p3 ∧ (p2 ∧ p3)) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319551314090586944707604924145 : (p4 ∨ (((False ∨ p3) ∧ (((p4 → p3) ∨ p1) ∧ (p4 ∨ p3))) ∨ (True ∧ (p4 → ((False ∧ (False ∧ (p3 ∨ ((p1 → p1) ∨ p5)))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113517741985070262592454661779 : ((((((p5 → p1) ∨ p2) ∨ ((p5 → p4) → (True → p3))) ∧ (p3 → (((p4 → False) ∧ True) ∨ (p2 ∧ False)))) ∨ (p3 → True)) ∨ (False → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350079790737053867797383857116 : (p4 → ((((((True ∨ ((False → ((p1 ∧ p3) ∧ p5)) → p3)) ∨ p3) → True) ∨ ((p1 ∨ (p2 ∨ p3)) ∨ (p1 ∧ p2))) → (False ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9979184404994960604082915778 : (((p3 ∧ (((p3 ∧ (True → (p2 → ((True ∨ p1) → ((((p2 → p2) ∨ p3) → (p2 ∧ False)) ∨ p4))))) ∨ p2) ∨ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120170875672689616109295065023 : ((((p2 → p1) ∧ (((((p3 ∧ p3) ∧ p3) → p2) → p1) ∧ ((p1 ∧ (p3 ∨ (p1 ∨ p5))) ∧ (p5 → (True ∨ False))))) ∧ True) → (p4 → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165741436568571220240902564544 : (((((p4 → p2) → p4) → p1) ∨ ((((p1 ∨ True) ∧ (p4 → p4)) ∨ (p1 ∧ p4)) → p2)) ∨ ((((p4 ∨ p5) → False) ∧ p4) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703112834226775556920280943950 : (((((p2 → p5) ∨ (p5 ∧ (((False → p1) ∧ p5) ∨ p3))) ∨ ((p1 → p4) → ((((p2 → (p3 ∧ True)) → False) ∨ False) ∨ (True ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65198031418682417904205372504 : ((p3 ∨ ((((p4 ∨ False) ∨ (((((p5 ∧ p4) → p1) ∨ (True → (p3 ∨ ((p2 ∧ p4) ∨ (p4 → True))))) → p5) → False)) ∧ p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261591289741530478586598361991 : ((p5 → p4) → ((p4 ∧ p2) ∨ ((p4 → (p3 → ((((p4 ∧ ((p1 ∨ True) → p5)) ∨ p2) ∧ (((False → p2) ∧ p5) ∧ p4)) ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644434632988761807234122698961 : ((((False ∨ (p3 ∨ (((p4 ∧ (p5 ∧ p3)) ∧ (p1 ∧ p4)) ∨ (((True ∨ (p3 → p3)) → ((p1 ∨ p5) → False)) ∧ (False → False))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230574880031214903502003957098 : (((p1 → p1) ∧ p3) → ((p5 ∧ ((((p3 ∧ p2) ∨ (False ∨ False)) → False) ∨ (p1 ∧ False))) ∨ (False → (p5 → ((p4 ∧ (p2 ∧ p5)) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149122752468670332797807224002 : (((p1 ∧ p3) ∧ ((p3 ∧ (True ∧ (p3 → ((p4 ∨ (p1 ∧ ((p4 → p4) ∧ p4))) ∨ p4)))) ∧ (True ∧ p5))) ∨ ((p2 → (p1 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180891751854534091188846348902 : ((((p4 ∧ p2) → True) → ((p4 → ((False → (p2 → p4)) → p1)) ∧ False)) → (((p4 → ((True → False) ∨ p1)) → ((p4 ∨ p4) → p3)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∧ p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((p4 ∧ p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h14
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135218416655628893384789397980 : (((((((p2 ∨ False) ∧ ((p4 ∧ True) ∧ p2)) ∨ (p4 ∨ False)) → p5) → ((p5 ∨ (p4 ∨ p5)) ∨ True)) → (False ∧ p5)) ∨ (p2 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118103985399081512170645151786 : ((False ∨ ((((True ∧ True) ∨ (((p1 ∧ False) ∧ p5) ∨ (False ∧ (p5 ∨ p4)))) ∧ (p3 ∨ (((False ∨ p1) ∨ p5) ∧ p4))) ∨ True)) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748238173686322164990848703188 : ((((p2 → True) → (((p5 → (((((p5 ∨ (False → p2)) → p1) ∧ True) → (p4 ∨ p3)) → False)) → p4) → (((p1 ∨ p2) ∧ p5) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232204950641785446217850291820 : (((False → p4) → p2) → ((p2 → p3) ∨ (((p2 → (((p5 ∨ True) ∧ (p3 ∧ p5)) ∧ True)) ∨ (p5 ∨ ((p2 ∨ (p5 → p1)) ∧ p3))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h19 := h1 h17
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204716534536574503843661290152 : (((True → (p1 ∨ (p4 ∧ p3))) ∨ p3) ∨ ((p3 → (False ∨ p5)) ∨ (True ∨ (p1 ∨ ((False ∧ True) ∨ ((((p1 ∧ p4) ∨ False) ∧ p1) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41682893020850176105632054888 : ((((p3 ∧ (p5 ∧ (p1 ∨ (False ∧ True)))) ∨ (((True ∨ ((p4 → ((True ∧ False) ∨ p2)) → True)) → ((True → True) ∨ False)) → p5)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299143856871459110151073792099 : (False ∨ ((((p5 ∨ ((False ∧ p1) ∧ p2)) → (((p1 → ((p5 → p2) ∧ ((p5 ∧ p2) → ((p4 ∧ p1) ∨ True)))) → p2) ∨ p5)) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8600158770054131579098524214 : ((((((((p4 ∧ p4) ∨ p5) → ((p2 ∧ p2) → True)) → (p2 → True)) → (p4 ∧ (((p3 ∧ p2) ∨ p4) ∧ p5))) ∨ (False → p3)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_165222469667385965484764358401 : ((((((p2 ∨ p4) ∨ p2) ∧ p5) ∧ ((((p3 ∨ p1) ∧ False) ∨ p1) ∨ p3)) ∨ (True ∨ p1)) ∨ (((p2 ∨ (p5 ∨ False)) → (p2 ∧ False)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175227860788341608917757511459 : ((p1 ∨ ((((((False ∨ p5) → p5) → p2) ∧ (True ∧ p3)) → p5) → (False ∧ p1))) → ((((p4 ∧ (p4 → p4)) ∧ True) ∧ p3) ∨ (p3 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191046042822925075933430207610 : ((((p1 ∨ p5) ∧ (p1 → p4)) → ((p3 ∧ p5) ∨ p1)) ∨ ((((p5 ∧ (p2 → (p4 ∨ True))) ∧ p3) ∧ ((p5 ∨ False) → (p5 → True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186795465457980444462946896545 : ((((p3 → (p1 → True)) → p1) ∧ (p4 → (p5 ∧ (False → False)))) → (((True ∧ (((p2 ∧ True) ∨ p5) ∧ (True → p4))) ∧ False) ∨ (p2 → p1))) := by
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
  have h5 : (p3 → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649881653053704169456050599424 : ((((((((p5 → False) ∧ (((p1 ∨ (True → True)) ∧ (p4 ∧ p5)) ∧ p5)) ∧ p2) ∨ (p4 → True)) ∧ ((False ∨ True) ∨ False)) ∧ (p2 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41916372940867839179894043672 : (((((p2 → p2) → p2) → (p2 ∨ ((((((False ∧ (((p1 ∨ p2) → p2) ∨ p4)) ∨ p1) ∨ p5) ∧ p4) → (p1 ∨ p2)) ∧ False))) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354604674311475999183268387107 : (p5 → (((((True ∨ (p1 ∧ ((((p1 ∧ p3) ∨ (p3 ∧ p5)) ∧ p4) ∨ (((p1 ∧ p2) → p2) ∧ (p5 → p2))))) ∧ p5) → False) ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684979694653252137635325156040 : ((((p3 ∧ (True → ((((p3 ∧ p2) → (p5 → p3)) ∧ (False ∨ (False → (p3 → p2)))) → p4))) ∨ ((p2 → False) → (True → (p1 ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173108896113729989151399405825 : ((p2 ∨ ((((p1 ∨ (p3 ∨ p5)) → (False ∨ p1)) → ((p3 → p5) → False)) ∨ True)) ∨ ((p3 ∧ p5) → ((p1 → (p3 → True)) ∧ (p1 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184287878155843377425647443154 : ((((((p1 ∧ p3) → p3) ∧ True) → (p3 ∨ (p5 → p3))) → False) ∨ ((True ∧ ((p4 ∧ p2) ∨ (((True ∨ p1) ∧ p5) ∧ p3))) → (p1 → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45607085754649635583165013369 : (((p3 ∨ ((p3 ∧ p1) → ((False ∨ True) ∧ ((False ∧ p2) → (p3 → ((p5 ∨ p3) ∧ (p2 ∨ ((p3 ∧ p3) ∨ (p1 ∧ p4))))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115847360131016084910673623103 : (((False ∨ ((p4 → True) → p5)) ∧ ((p3 → False) → (((p4 ∧ True) ∧ (p5 ∨ p3)) → ((False ∧ (p4 ∧ p5)) ∧ (True ∧ True))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40190341810136309944346877610 : ((((((p3 ∨ p5) ∧ True) ∨ (((True → ((p5 → p3) ∨ (((False ∨ p1) ∧ (p3 ∧ p4)) ∨ p3))) ∧ (p4 ∧ True)) ∧ p5)) ∧ p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41790624062603796209055323930 : (((((True ∨ p2) ∧ (p1 → p4)) → ((False ∧ ((p4 → p3) ∧ (p3 ∧ (p2 → (p3 ∧ ((p2 ∨ p1) ∧ (True → p3))))))) ∨ True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856005440128259768027992205419 : ((((((((p2 ∧ ((p1 ∨ (False → p5)) ∧ ((True ∨ ((p3 ∧ False) → p4)) ∨ (p3 ∨ True)))) → p4) → p1) ∨ (p2 → p2)) ∨ False) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 ∧ ((p1 ∨ (False → p5)) ∧ ((True ∨ ((p3 ∧ False) → p4)) ∨ (p3 ∨ True)))) → p4) → p1) ∨ (p2 → p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137154346265961943626141936071 : ((False ∧ (((p4 ∨ ((p3 ∨ True) → (((False ∧ p1) → (p1 ∨ p3)) → (p1 ∧ ((p2 ∧ False) ∧ p4))))) ∨ False) ∨ True)) ∨ (p2 → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656511179008661318413087993949 : (((((p2 ∧ (p4 ∨ (p3 ∨ ((p1 ∧ p3) → (p5 ∨ True))))) → ((True → ((p4 → (False → False)) ∨ (True ∧ p5))) → p1)) ∨ (False → False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_122102765365411529948851284905 : (((p5 → (p5 → (((p2 ∨ ((p2 ∨ p4) → False)) ∨ ((((False ∨ True) ∨ (p3 ∧ True)) ∧ p5) ∨ (p2 ∧ False))) ∧ True))) → p3) → (p3 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p5 → (((p2 ∨ ((p2 ∨ p4) → False)) ∨ ((((False ∨ True) ∨ (p3 ∧ True)) ∧ p5) ∨ (p2 ∧ False))) ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148983573329697971218850834348 : (((p4 ∧ (p5 → p3)) ∧ (((p3 ∧ (True ∧ ((p1 → False) → p5))) ∧ (False ∧ (False ∧ p5))) ∨ (p4 → p1))) ∨ ((p4 → p4) ∨ (False ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



