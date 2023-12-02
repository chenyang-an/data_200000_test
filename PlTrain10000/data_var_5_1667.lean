variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338221033726384927697575283015 : (p1 → ((((p5 ∨ (False ∧ False)) ∧ p1) ∧ False) ∨ (p3 → (p5 ∨ (((True → (p1 ∨ ((True ∧ False) ∨ p3))) ∨ False) → (p1 ∧ (False → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186635694559619537989864696446 : (((p3 ∨ ((p2 → (p5 ∨ (p1 ∧ p4))) ∧ p2)) → (p5 ∧ p3)) → ((False ∨ p3) ∨ (False ∨ (p2 ∨ (p3 ∨ ((False → p5) ∨ (p5 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114974442163030016014868876834 : (((((p2 ∧ p2) ∨ (True ∧ (p4 ∨ ((p3 → False) ∧ False)))) ∧ False) ∧ (((True → ((False ∨ (p3 → p2)) → p1)) → p3) ∨ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263796681562904552755917624841 : (True ∧ (((False → (p2 ∨ ((True ∨ ((p3 → p5) ∧ (p4 ∨ p3))) → False))) → (p2 → p3)) ∨ ((False → p4) ∨ ((p4 ∧ (p2 ∧ True)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_329646505106930109088639254991 : (True → ((p3 ∧ True) → ((((False ∨ (p2 ∧ (((p5 ∨ p2) → ((p5 ∧ p3) ∧ ((p2 → p5) ∧ p1))) → p2))) ∧ (p2 ∧ p1)) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190088276842446719813091550366 : ((((False ∨ (p3 ∧ (p1 ∧ p1))) ∧ (p4 → True)) ∧ True) ∨ (p4 ∨ (p4 → ((p1 → (True ∨ (True ∧ ((False → p2) ∧ p1)))) ∨ (p2 ∧ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105303740430488646961635025956 : (((p2 ∧ ((True ∧ (p2 ∨ ((((False → p5) ∧ p5) ∨ False) ∨ (p5 ∧ (False ∧ False))))) ∨ (p4 ∧ p4))) → (p1 ∨ (p1 ∨ p2))) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134172016604282937758037715469 : ((((p3 ∧ (((p4 → (p1 ∧ ((p4 ∧ p2) ∧ p1))) → (p5 ∧ p4)) ∧ p2)) ∨ ((p3 ∨ True) ∨ (p1 → p2))) ∨ p2) ∨ (False ∨ (p2 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_124039447515643530050353881542 : (((((((p5 → False) ∧ p2) → p2) ∧ (True → (p2 ∧ False))) → p4) → (((False ∨ (False ∨ ((p2 ∨ True) → p4))) ∧ p5) ∧ False)) → (p1 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 → False) ∧ p2) → p2) ∧ (True → (p2 ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((((p5 → False) ∧ p2) → p2) ∧ (True → (p2 ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h11
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218378436849059017802469527917 : (((p4 → p5) ∨ (False ∧ p1)) → (((p4 ∨ p4) ∧ ((p5 ∨ False) ∧ (p3 → (((p5 ∧ True) → p4) ∧ (True ∧ p4))))) ∨ ((p3 → p5) ∨ True))) := by
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
theorem thm_5_vars_148385194797551570269139320227 : (((((p1 ∧ p1) ∧ (p1 ∧ p1)) ∨ ((True → p3) ∨ ((p5 ∨ p2) → p1))) ∨ (False ∨ (p4 → (p2 → p2)))) ∨ (p2 ∨ (p3 ∨ (p3 ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243423421224210454772369392531 : ((p5 → True) ∧ (((((p3 ∧ p4) → True) ∨ True) → (p5 ∧ (p1 → p4))) → ((p5 ∧ ((p4 ∧ True) → p5)) ∧ (p5 ∨ ((p3 ∧ True) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∧ p4) → True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (((p3 ∧ p4) → True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : (((p3 ∧ p4) → True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336159869320993374855108668851 : (p1 → (((((p5 ∧ ((p4 ∨ p4) ∧ p3)) ∨ ((p2 → (((p2 ∧ (p2 → p1)) → p4) → p3)) → p2)) → ((p3 → p2) ∧ True)) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323487012751477731118812535759 : (p5 ∨ (((p3 ∧ ((((p4 ∨ ((p1 ∨ p5) ∨ p5)) → False) ∨ p4) ∨ (((p3 ∨ p2) → p3) → p3))) ∧ (p2 ∧ True)) ∨ (False → (False → p2)))) := by
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
theorem thm_5_vars_261088514802637674591355091728 : ((p4 → p3) → ((True → ((p3 → (p1 ∨ ((p4 → (p4 ∨ (p5 ∧ (p2 ∧ True)))) ∧ False))) → (p4 ∨ (True ∧ True)))) → (p3 ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149615972133974806683469915081 : ((p3 ∧ (p5 ∧ (False ∧ (((p4 ∧ p1) → p3) ∨ ((p1 → p3) ∧ ((((True ∧ p2) ∧ p2) → True) ∧ p5)))))) ∨ (p3 → ((p5 ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42953190456017324814278965371 : (((p4 → (p3 ∨ ((p2 ∨ p5) → (((p1 → p3) → ((((p1 ∨ False) ∨ (p1 → ((False ∧ p3) ∨ p2))) ∨ p1) → False)) ∨ p4)))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4146961151255135228327611917 : (p4 ∨ ((((True ∨ p3) ∧ (p3 ∨ p2)) → (p2 → (((False ∧ p5) ∧ (True ∨ p1)) ∨ ((p4 ∧ (False ∧ (p2 ∧ False))) → p1)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202581492216416327262293080751 : (((False → (p5 → p1)) ∨ (p5 → p4)) ∧ ((p1 → ((p2 ∨ p1) ∧ False)) ∨ ((((((p2 ∨ (False ∨ True)) ∨ False) → False) ∧ p3) ∧ True) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 ∨ (False ∨ True)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621803562801978089754050643632 : ((((p1 ∧ ((((p4 ∧ ((p5 ∧ (((p2 → (p2 → (p4 ∨ p2))) → p2) ∧ (False ∨ p1))) ∧ False)) ∨ p4) → p2) → (p5 ∨ p2))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_39392289465027086229384055152 : (((p4 ∧ ((((True ∧ ((False ∨ (((p1 ∧ (p5 ∨ p3)) ∧ (True ∨ ((p3 ∧ False) ∧ p5))) ∧ p1)) ∧ p3)) ∨ p4) ∨ True) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704902304902109308583075769814 : ((((p3 ∨ ((p3 → p5) → ((p2 ∧ p2) ∨ (True ∧ False)))) → ((((p5 ∧ ((p1 → p1) → False)) ∨ (p2 → p4)) ∧ p1) ∨ (True ∨ p3))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325735969311786462066497438544 : (p5 ∨ (p2 ∨ ((True ∧ ((p4 → ((((p5 → p5) ∧ (True → p1)) ∧ (p4 → p2)) → p5)) ∧ (p3 ∨ (((p3 ∧ p5) ∨ False) ∧ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50221650786880834153368196550 : (((((p4 ∨ p5) → ((p2 ∧ False) ∧ ((p5 ∨ (((False ∨ p2) ∧ True) ∨ p3)) → (p2 → p1)))) ∨ p2) ∨ ((p2 ∨ True) → (p3 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172963943546365171680502004174 : ((p4 ∧ (((((p2 → False) ∧ p3) → True) → ((p4 ∧ p3) ∨ True)) ∧ (p3 ∧ False))) ∨ (True ∨ (((p1 ∧ (p5 → (False → p5))) ∨ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111666947571040131562929666083 : ((((p3 ∨ (((p5 ∨ p1) ∨ (False ∧ p2)) ∨ (p3 ∧ (((p2 ∧ p2) ∧ (p3 → p2)) ∧ ((p5 ∧ p3) → p2))))) ∨ p1) ∨ True) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38402247840133391279815480640 : ((((p1 → ((((p1 → ((p2 ∨ p3) ∧ p2)) ∧ p5) → (p3 → (p3 → p5))) ∨ p3)) → ((p2 → ((p4 ∨ p5) ∨ p4)) ∧ True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329708523962181949363463526917 : (True → ((False → True) → ((((p2 ∨ ((p2 ∧ ((True → ((True → p3) ∧ (True ∧ True))) ∨ False)) → p5)) ∧ (p1 → p3)) ∨ True) ∨ (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232880284135346191641311814845 : ((p2 ∧ (p5 → p3)) → ((p1 ∧ (p4 ∨ (((False ∧ True) ∨ p5) ∧ ((False → p4) ∧ (p4 ∨ ((False → p2) ∧ True)))))) ∨ (False ∨ (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165116127287876652247998740410 : (((p4 → ((p1 → (False ∨ ((p3 ∧ p1) ∨ ((p5 → (p1 ∧ False)) ∧ p4)))) ∧ p4)) → p1) ∨ (True ∨ ((p5 → True) ∨ (p4 ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207382749847278399950980787197 : (((False ∧ (p1 ∨ (True ∨ p5))) ∨ p1) → (p5 → (((p4 ∨ p3) → (((p4 ∧ (p2 → (p2 → p2))) ∧ (p5 ∧ p5)) → (p2 ∧ p3))) ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592605538066700169691354601647 : (((((p1 ∨ ((((True ∧ p2) ∧ ((p3 ∨ ((((p4 ∨ p2) ∨ p3) ∨ p2) ∨ p5)) ∨ (p1 → p2))) ∨ p5) → p4)) → (p5 ∧ p1)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323808025881832874406707745436 : (p5 ∨ ((p1 ∨ ((True ∧ (p2 → (True → (((p5 ∨ (p2 ∧ (p1 ∧ p5))) → p3) → p5)))) ∨ True)) ∨ (False ∧ ((False ∨ p5) ∧ (p5 ∧ p2))))) := by
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
theorem thm_5_vars_636866909449673459963792877820 : ((((((p1 → False) ∨ ((p2 → (p2 → ((p4 ∧ p3) ∨ p3))) ∧ (p3 ∧ False))) → ((p1 → p3) ∨ ((p4 → p1) → (p3 → p2)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590644575892354383491554093015 : (((((p3 ∧ (((p1 ∨ (p5 ∧ (True ∨ (((p3 → p1) → (p4 ∨ p5)) ∧ p1)))) → p3) ∧ ((p3 → p1) → (p1 ∧ p2)))) → p5) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917666535053637325357097311251 : (((((p1 → (p2 → (True ∨ ((False ∧ p5) ∨ True)))) ∨ (((p5 ∨ p3) → True) ∧ p3)) → (p1 ∨ ((p3 ∨ (p5 ∨ True)) → (p4 ∧ False)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p2 → (True ∨ ((False ∧ p5) ∨ True)))) ∨ (((p5 ∨ p3) → True) ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∨ (p5 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166733278131666060839104925614 : ((p4 → ((True → (p1 → ((True ∧ p4) ∨ ((p2 → (p3 → (p5 ∧ p1))) → p1)))) ∧ False)) ∨ (((p2 ∨ (p1 ∧ p3)) ∨ p4) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59802827394590807455616740698 : (((p2 ∧ p4) → ((((p1 → p2) ∧ p5) ∨ p3) ∨ (((p5 ∨ p5) ∨ (((True ∨ p3) → p2) ∨ p1)) → (((False ∧ True) ∨ True) ∨ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752264024983956989273089268543 : (((True ∧ (p5 → (((((p2 ∨ p1) ∧ p2) ∨ ((p1 ∨ (p1 ∨ (p1 ∨ p4))) ∨ ((p2 ∧ p1) → ((True ∨ p1) → p3)))) ∨ p5) ∨ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251643659999744186079964563882 : ((p3 → p1) ∨ (p3 ∨ ((((p5 ∨ p5) ∧ False) ∨ p5) ∨ (((p4 → p5) ∧ ((p2 ∨ p5) ∧ True)) → (((p1 ∨ True) ∨ (p2 ∨ p3)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40271188002006122213814155653 : ((((p5 ∨ (True → (False ∨ (p5 → ((p2 ∨ (p2 ∧ (((p5 ∨ (p5 ∨ p4)) ∨ (p3 → p2)) ∧ (False ∨ p5)))) ∧ False))))) ∧ p5) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193136889775424675508083580345 : ((((p3 ∧ p2) ∨ (p1 → p1)) ∨ (p2 ∨ (False → p1))) → (((p2 ∨ p1) → False) ∨ ((False → (((p3 ∧ (p3 → p1)) ∨ p5) → p1)) ∨ False))) := by
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h6
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h21
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215097524437088501570873725830 : (((p1 → False) → (p4 ∧ False)) ∨ (((False ∧ p5) ∨ ((p4 ∧ p3) → (p3 ∧ ((p1 → p2) ∧ p5)))) ∨ (((p5 ∨ p4) ∨ p4) → (p2 → True)))) := by
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
theorem thm_5_vars_152113129532780937958020470484 : ((((((False → p5) ∨ p1) ∧ (p5 → p3)) ∨ p4) ∧ (p4 → (((p1 ∨ p5) ∨ (p2 ∨ (False → p3))) → p2))) → ((p3 ∨ (True ∨ p3)) ∨ p2)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763618963750618910176636284107 : (((p3 ∧ (p5 ∧ ((p3 → (((p1 ∧ ((p5 → p1) ∧ ((False ∧ p3) → (p2 → p2)))) ∨ (p5 ∧ (p4 ∨ p5))) ∧ (p2 → p3))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181421899125361552801506831323 : ((p2 ∨ (True ∨ (p4 ∧ (p3 → (p4 ∧ ((True → (p4 ∨ p3)) ∨ p5)))))) → (p2 → (((False ∧ (p1 ∨ p4)) ∨ (True → True)) ∨ (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312930558335116265179378441594 : (p3 ∨ ((p2 → ((((p4 ∨ (((p1 ∨ p5) ∨ p4) → p4)) ∧ False) ∨ p3) ∨ ((((True → (p5 ∨ p3)) ∧ False) → (True → p3)) ∧ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41849809916202292434460952587 : ((((p3 → (False → False)) ∧ (((False → p2) → (p5 ∧ (((p4 → False) ∧ p4) ∧ True))) ∨ (((p1 → (False ∨ True)) ∨ False) ∨ True))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222316879648580391852503753760 : (((p1 → p3) → True) ∧ ((((p3 ∨ (p4 ∨ p2)) ∧ (p2 → (((False ∧ p4) ∨ (p2 ∨ False)) ∨ p2))) → p5) ∨ ((p3 ∧ (False ∨ p1)) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669895208655562591064477103577 : (((((((p5 ∧ p2) ∨ p5) → ((True ∨ True) ∨ ((True ∧ p1) ∨ p4))) → ((True → ((p3 ∧ False) ∧ p3)) ∧ False)) ∨ (False → (p2 ∧ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191569062919448280559060803530 : ((p2 ∧ (((p2 → (p2 ∧ p3)) → (True ∧ p1)) ∨ p4)) ∨ (p3 → (p1 ∨ ((p5 ∨ ((p1 ∧ ((p3 → False) ∧ (True ∨ p1))) → True)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55160666093933200421199244439 : ((((p5 ∧ ((False → p3) ∨ True)) ∨ p4) ∨ (p5 ∨ ((p5 ∨ p1) → (((p3 → p1) ∧ True) ∨ ((p5 → (False → (True ∧ p5))) → p5))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313978212092190025242192679686 : (p3 ∨ (((((True ∨ (p2 ∨ p5)) → ((p5 ∨ p5) ∧ p5)) ∨ False) → ((((((p4 ∧ False) ∨ p5) → False) → False) ∧ True) ∨ p3)) ∨ (False ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ (p2 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 ∧ False) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308277867823127589520454339039 : (p2 ∨ ((p4 ∨ ((((p1 ∧ (p5 ∨ ((p5 ∧ p2) ∨ (False ∨ (p3 ∧ False))))) ∨ (p5 ∨ False)) ∧ ((False → p3) → (p3 ∧ p2))) → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h8
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- False on the left can always be used.
          apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h23
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135283752156641472992321556780 : (((p1 → (p3 ∨ (((p3 → (p3 ∨ p5)) → (False ∧ p4)) ∧ ((p4 ∨ p3) ∧ (p2 ∨ (p2 ∨ p4)))))) → (p4 ∧ False)) ∨ (p4 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257126287881068001011799887081 : ((p2 ∨ p1) → (((False ∧ p2) ∨ (((False ∧ (((((True ∧ p4) → False) → p1) → (False → (p5 ∨ p4))) ∧ p3)) ∧ p3) ∧ (True ∨ p5))) ∨ True)) := by
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
theorem thm_5_vars_774801545193321728896427593490 : (((False ∨ (((((False ∨ p3) ∨ p2) → True) ∨ p5) → ((((True ∨ (p4 ∧ p5)) ∧ (((p5 ∨ False) ∧ p1) ∨ (False → p5))) ∨ p1) ∧ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636002254177569701320265316397 : ((((((((p2 ∨ p3) → (False → p2)) ∧ (False → p1)) ∨ (p4 → ((p5 ∧ p1) ∧ p3))) ∧ ((False → ((True ∨ False) ∨ True)) ∨ p5)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200058404470883930907374428135 : (((p2 → ((p2 ∧ False) → p5)) → (p2 ∨ False)) → ((False ∨ (p1 ∧ (((p5 → (((False ∧ p3) → False) ∧ p1)) ∨ p5) ∧ p2))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802406990051307088281934105719 : (((p2 → (False ∨ (p5 ∧ (((False ∧ (p3 ∨ ((p2 → p3) ∧ p1))) ∧ (p3 ∧ (p1 ∧ (p3 → False)))) ∧ ((p2 ∧ p3) → (False ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134663716405976760693519310500 : (((((((p3 ∨ p5) → (p3 ∨ True)) → (True → True)) ∨ p5) → (((p5 → ((p4 ∧ True) ∧ p5)) ∨ False) ∧ p1)) → p3) ∨ ((p5 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206419318013931158497257693494 : ((p3 ∨ (p2 ∨ (p4 → (p3 ∧ p2)))) ∨ ((p2 ∨ (p4 → ((p2 → p3) → ((p2 → p4) ∧ p4)))) ∨ ((p4 ∧ (p5 ∧ p1)) → (p3 ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351697454819360918813536915569 : (p4 → ((((((p4 ∧ p3) ∨ p4) ∨ (p5 → p3)) → (p1 ∨ p2)) ∨ (p5 → True)) ∧ (((p1 ∧ p2) ∧ p1) → (((p4 ∨ True) ∨ p5) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176972383091601313814514309477 : (((False ∨ p1) → ((p3 ∨ p4) ∨ ((p4 ∨ (p3 ∨ p3)) ∨ (p5 ∨ True)))) ∧ ((True ∨ ((p1 ∨ True) → ((False → (p4 → p2)) ∧ p3))) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178751431153267219444767676613 : ((((False ∨ p2) ∧ p5) ∧ ((p2 ∧ ((False ∧ p3) → p1)) ∨ (p2 → p2))) ∨ ((p1 ∨ (p4 ∧ True)) → (p4 ∨ (p1 ∨ ((False ∨ p1) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259870015739252449742335677754 : ((p1 → p4) → (((p1 ∧ ((p1 ∧ (p5 ∨ ((p1 ∧ (p4 ∧ p5)) ∨ p3))) ∧ (p4 → ((True → p3) ∨ (p5 ∧ p4))))) ∨ p4) → (p2 ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h20 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h20
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877530112336382403818231312 : ((True → (True → ((((p1 ∨ (p2 → (p2 ∨ (False → False)))) ∨ (p4 → p2)) → p1) ∨ (p3 ∨ (False ∧ ((p4 ∨ p5) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1794345357648088074444610723 : ((((False ∧ p4) ∨ (p5 → False)) ∧ (((((False → False) ∨ False) ∨ (p4 → p1)) ∧ (False ∧ (p5 ∨ p5))) ∧ p2)) ∨ (p5 → (True ∧ True))) := by
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
theorem thm_5_vars_732161917552935599111568421410 : ((((True ∧ p4) ∧ (((p4 ∧ (((True → p2) ∨ (True → (((((p4 → False) → (p4 ∨ p5)) ∨ p2) → p4) ∧ p4))) → p5)) ∧ p5) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337363438521200658457221537962 : (p1 → ((((p5 → (p1 ∨ (p2 → (p3 → ((False → (p3 ∧ p5)) → p2))))) → p3) ∧ (((p3 → False) ∧ p3) → p2)) ∨ (p1 ∧ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198246416741435583282396355230 : ((True ∧ (p4 ∨ (((False ∨ p1) ∨ p5) ∧ False))) ∨ (p5 ∨ ((((False ∨ p2) ∨ False) ∨ p3) → (True ∨ ((True → (p4 → p3)) → (True → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357010917064328452233788261734 : (p5 → (((p3 ∨ p3) ∨ p2) ∨ ((((False ∧ p4) ∨ (p5 ∨ (False ∨ p4))) ∨ p3) → ((p4 ∨ ((False → True) ∨ ((p5 → p2) → True))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252589886950351141422376841007 : ((p5 → p3) ∨ ((p5 → (((((True → (p2 ∨ p2)) ∧ False) → p4) ∧ p2) ∨ (p1 ∨ (False ∧ p3)))) → (p5 → (((True → False) ∨ p3) → p3)))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37349353127940237311245078187 : ((((((p5 ∨ ((p2 → p4) → (((p3 ∧ p2) ∧ (p2 ∧ p5)) ∧ (p1 → ((p2 ∧ (False ∧ p4)) ∨ p4))))) ∧ p3) ∨ p3) ∨ True) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149918026379080116427555590279 : ((p3 ∨ ((p1 ∨ (p3 ∧ (p4 ∨ ((False ∨ ((p4 ∧ (((p3 → p2) ∨ p2) ∨ p3)) ∧ p2)) → True)))) → False)) ∨ ((p5 ∧ p5) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164763531378076367554712731857 : ((((((p2 → (p1 ∨ p4)) ∨ ((p3 ∧ False) → p3)) ∨ False) → ((False ∨ p3) ∧ p5)) ∨ p1) ∨ (p3 → (True ∧ (True ∨ (p2 ∨ (False ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177932272790049397200639038751 : ((((False ∧ (p4 ∧ (p4 ∧ p3))) ∨ (((p1 → p5) → p4) → p4)) ∨ True) ∨ ((p3 ∨ (True ∨ ((False → False) ∧ ((p4 → p2) → p2)))) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337491535425154058087738536998 : (p1 → ((((((p3 ∧ False) ∧ (p4 ∨ p3)) ∨ p2) ∨ p1) ∨ ((True → p4) → (p5 ∨ (p4 ∧ (p1 ∨ p2))))) ∧ (False → (False ∨ (p3 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713784648057085930011294139315 : ((((((p2 ∨ (p1 → False)) ∧ True) ∨ p3) → (((p5 → (((False → ((False → p1) ∧ False)) → (p3 ∧ p1)) → p2)) ∨ p2) ∨ (p5 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258054894300297637707844553897 : ((p4 ∨ p2) → (((p3 → p3) → (((p4 → (((p5 → p4) ∨ (p5 ∨ p3)) → p1)) ∨ False) ∧ False)) ∨ ((False → (p3 → p1)) ∨ (p5 → p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113893056361011486312675742107 : ((((p2 ∨ (((True ∨ (p4 ∧ (p1 ∧ p1))) → ((p3 ∧ (p5 ∧ (p1 ∨ p4))) ∨ p3)) → p2)) ∨ p4) ∧ ((p2 ∧ p2) ∧ False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136293054337599082316863262974 : (((p1 ∨ ((p4 ∨ (p4 → p2)) → p4)) → (p4 → ((((p4 ∨ (p1 ∧ ((p1 ∨ False) ∨ p4))) → p3) ∧ p1) → p5))) ∨ (True → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315132034361841698620567271509 : (p3 ∨ ((p3 ∧ ((p2 ∨ (False ∧ p1)) ∨ p1)) ∨ ((p3 ∨ p2) → (True ∨ (((p3 → p2) ∨ (p2 ∨ False)) → (p5 ∨ ((p5 ∨ p3) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133867734360722773809263787230 : (((p3 ∧ ((((p1 ∧ (p1 ∧ p2)) ∨ ((((p2 → p1) ∧ True) ∨ p5) ∧ (p1 ∧ False))) ∧ (False → p3)) ∨ p2)) ∧ True) ∨ (True ∨ (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50214477843889944428892294584 : ((((((((True ∨ p3) ∧ p4) ∧ p2) ∨ (p2 ∨ p1)) ∧ ((False → (p5 → p5)) ∨ (p2 ∨ True))) ∨ False) ∨ ((p4 ∨ p4) ∨ (p5 → True))) ∨ p1) := by
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
theorem thm_5_vars_40782117918214385624629423356 : ((((p1 ∧ (p5 → ((True ∨ (((((p4 ∧ (p4 → (p3 ∧ p1))) ∨ p1) → True) → p3) ∨ False)) → ((True → p3) → p3)))) → p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147399163886771211956709244839 : ((((p2 ∨ (p5 ∧ (True → (p2 → False)))) ∧ ((((((p5 → False) → p3) ∨ p4) → p1) → p1) ∧ p1)) ∨ p1) ∨ ((p4 ∨ (False ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215174994092710476401693781309 : ((True ∧ ((p3 ∧ p1) → p2)) ∨ (((p4 ∧ (((p5 ∧ (p4 ∨ ((p1 → (p4 ∨ p5)) → p2))) ∨ p3) ∨ p4)) ∧ True) ∨ (p5 → (True ∨ False)))) := by
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
theorem thm_5_vars_51868377004793321420878903193 : ((((((True → (False → False)) ∧ p2) ∧ (True ∧ (p3 ∧ ((p1 ∧ p3) ∨ p5)))) ∨ p3) ∨ (((p3 ∨ p2) ∧ p1) ∧ ((p5 ∧ p3) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310150461708612074162103681215 : (p2 ∨ (((p3 ∨ (p4 → ((p5 → p4) → (p5 ∨ (p5 ∨ True))))) ∨ (p3 ∧ False)) → (False ∨ (p4 → (((p3 ∨ p2) ∧ False) ∨ (False → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50271911183093108310643473899 : (((((p1 ∨ (p1 ∧ (((p2 → ((p2 → False) ∨ (p2 ∨ True))) ∧ p2) ∨ False))) ∧ p2) ∨ (False → False)) ∨ ((True ∨ (p3 ∨ p4)) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59938998036511611328023172040 : (((True ∨ False) → (p4 ∧ ((p4 ∨ (((p5 → True) → p3) ∧ ((p3 → (False ∨ p3)) ∨ (True → (p3 ∧ p3))))) ∧ ((p4 ∨ p2) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208957693889845052489947681151 : ((True ∨ ((False ∧ (p4 → p3)) → p2)) → (((p4 ∧ p1) → p5) ∨ (((p1 → True) → False) ∨ (True ∨ (p5 ∨ (p4 ∨ ((p3 ∧ True) → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65989273309785357794339043018 : ((p4 ∨ (p2 → (p2 → ((True ∨ p2) → ((p4 ∧ ((p2 ∧ (False → p3)) ∧ p3)) ∨ (((p2 → False) ∨ ((p3 ∨ p2) ∨ p5)) ∨ True)))))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
theorem thm_5_vars_687486970365674964409250149040 : (((((False ∧ (p5 → ((True ∧ (p4 ∨ (((True → p3) ∧ p2) ∨ p1))) ∧ p1))) ∨ False) ∧ (p4 ∨ (((p4 ∨ (p5 → p5)) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88710234626549168541827531044 : (((((p3 → False) → p2) ∨ True) → ((False → ((((((p4 → p2) ∧ (p1 ∧ p3)) → p4) → True) ∨ ((p2 → p3) ∨ p2)) ∧ p1)) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → False) → p2) ∨ True) := by
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
theorem thm_5_vars_200764840468003965922942374676 : ((p4 ∧ ((p1 → ((p4 → p2) ∧ p5)) ∨ p1)) → (p1 ∨ (p3 ∨ (p2 ∨ ((p1 → ((((p2 ∨ p5) ∧ p3) → p3) ∧ (p2 ∧ p5))) ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- One of the premise coincides with the conclusion.
    exact h15
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305160576264716579115476372360 : (p1 ∨ ((((((p1 ∧ p4) ∧ p3) ∨ p2) ∧ (p5 ∨ ((p2 → (p4 ∨ ((p2 → True) ∨ p2))) → True))) ∨ False) ∨ (False ∨ (p3 ∨ (p5 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84798408262669400920873848032 : (((True ∧ (((((p4 → True) → (p4 → False)) ∨ True) ∧ (True → p2)) → p5)) ∧ (((((p1 ∧ (False ∨ p4)) ∧ p5) ∨ True) ∨ True) → p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((((p1 ∧ (False ∨ p4)) ∧ p5) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175367175640760210793250912501 : ((True → (((((((p4 → (True → False)) ∨ p3) ∧ False) ∧ True) → p5) ∨ False) ∧ p1)) → (((p3 ∧ False) ∧ ((p1 ∨ p1) ∧ (p1 → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



