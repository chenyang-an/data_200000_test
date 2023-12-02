variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218468242903669783508461219768 : (((True ∨ True) → (p1 ∧ False)) → ((p3 → ((p2 ∧ p3) ∨ ((p5 ∧ ((((False ∨ (True → p1)) ∨ p2) ∧ p2) ∨ (p4 ∧ p5))) ∨ p2))) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330721930485671297178865915929 : (True → (p1 → ((((p5 → (((True → (p3 ∨ p5)) ∧ (p2 → p4)) ∨ p5)) ∨ p5) ∧ ((p4 → (True ∧ (False ∨ p5))) ∧ (p4 ∧ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111786701739922642527906310203 : (((((p4 → (False ∧ (((p1 ∨ p5) → p4) → p3))) ∨ ((((p2 → (p3 ∧ p1)) ∨ p2) ∧ p3) ∧ p3)) ∨ (p1 ∧ p5)) ∨ p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53157504107130805917773833310 : (((((p4 ∧ p5) ∧ ((False ∧ p2) ∨ ((False ∨ p2) → True))) ∨ p2) ∨ (((p3 → (p2 ∧ p3)) ∧ (p3 ∨ ((p5 ∨ False) ∨ True))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341721208917936987736739625384 : (p2 → (((((p3 → (p4 → False)) ∧ p5) ∧ p1) ∨ ((False ∨ ((p2 → (p4 → ((p3 → p5) ∧ p4))) ∨ (p1 ∨ False))) ∧ p5)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258071657765245700423904494939 : ((p4 ∨ p2) → ((p5 → p1) → (((((((p4 ∨ ((p4 ∨ ((p5 → p5) → p1)) ∧ True)) ∨ p5) → p1) ∨ p1) ∨ True) ∨ p1) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209419453584417485909120961830 : ((p2 → ((True ∨ (p3 ∧ False)) ∨ p4)) → (p5 → (((((p4 ∨ False) ∧ (p4 ∨ True)) ∧ (p5 ∧ ((p1 ∧ p4) → False))) ∧ (p1 ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314696645355242307436695570721 : (p3 ∨ ((True ∨ ((((p5 → p4) → True) → p3) ∧ (p5 ∨ (p2 → ((False → p4) → p1))))) → (((False ∧ p4) ∧ ((p4 → p1) → p5)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205131492322846274715956946461 : ((((p3 ∧ p5) → p5) ∧ (p4 → p3)) ∨ ((p5 ∨ ((((p5 ∨ (((p1 ∧ (p5 ∨ True)) ∧ (p1 → p4)) → p3)) ∨ True) ∨ False) ∨ False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114401307240426184943774475851 : ((((p1 ∨ ((p4 ∧ (p2 ∨ (p4 ∧ p4))) ∨ p4)) ∨ (True ∧ ((p3 → (p4 ∧ p2)) ∨ p5))) ∨ (p1 → ((p2 ∨ p4) → True))) ∨ (p1 → p2)) := by
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
theorem thm_5_vars_53765635351316791490775178761 : ((((p4 → (p2 ∨ ((p1 ∧ (p4 ∨ p3)) → p3))) ∧ p5) ∨ ((p1 ∧ (p1 ∨ (True → ((False ∧ ((p2 → p3) ∧ p3)) → p2)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_933066496921373953283034209656 : ((((True → ((False ∨ p5) ∧ ((False ∨ p5) ∧ p4))) ∧ ((((True ∧ p4) ∨ (p5 ∧ (p2 → p3))) ∧ ((False → True) ∨ p3)) ∧ (p1 ∨ p3))) → p4) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h21 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h32 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h34 := h2 h33
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- We need to get the right conjuct of h35 based on <expert-advice>.
        let h36 := h35.right
        -- One of the premise coincides with the conclusion.
        exact h36
      case inr h37 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h39 := h2 h38
        -- We need to get the right conjuct of h39 based on <expert-advice>.
        let h40 := h39.right
        -- We need to get the right conjuct of h40 based on <expert-advice>.
        let h41 := h40.right
        -- One of the premise coincides with the conclusion.
        exact h41
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116564473084977366672838067418 : (((p2 ∨ p2) ∧ ((True ∨ (p4 ∧ ((p5 ∨ p4) → ((((p5 → p5) ∧ p3) ∧ (p2 → False)) ∧ (p3 ∨ p2))))) → (p4 → p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149157713172590276390802001007 : (((p2 ∨ p2) ∧ ((p2 ∧ ((((p2 → True) ∧ (p5 ∨ p1)) → ((p5 ∨ p1) ∨ p4)) ∧ p3)) ∧ (p1 → p4))) ∨ ((p3 ∧ (p3 → p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37580295308513366358020519588 : ((((p1 → ((((True ∨ ((True ∨ (p3 ∨ True)) ∨ p4)) ∧ (p1 ∨ p4)) → p3) ∨ (((p3 ∧ (p3 ∧ p4)) ∨ p4) → p1))) ∨ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738879500563276732502830095661 : ((((p3 ∧ True) ∨ ((False ∧ p3) ∨ (((((p3 ∨ p3) → p5) ∨ (p3 → p3)) ∨ ((p4 ∧ p5) → ((p4 → (p4 ∨ p5)) → p3))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304871173174979631536778006153 : (p1 ∨ (((p4 ∨ p1) ∨ (((p3 ∧ True) ∧ ((False → p2) ∨ (p4 ∨ p3))) ∨ (p4 ∧ (((p4 → p5) ∨ (p5 ∧ False)) ∧ True)))) → (False ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
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
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
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
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219552338136845881701374951210 : ((True → ((True ∨ p5) ∧ p3)) → (((True → p1) → ((((p1 ∧ (p2 ∨ False)) ∧ p1) ∧ (p2 ∨ (True → p2))) → ((p1 ∧ p4) → p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314321911543936397943078686980 : (p3 ∨ (((((True ∧ (p5 ∨ p4)) → p3) ∨ True) ∧ ((False → (p4 ∧ ((p1 → False) ∧ (p4 → (True ∧ False))))) → p5)) → (False ∨ (p4 ∨ p5)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p4 ∧ ((p1 → False) ∧ (p4 → (True ∧ False))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (False → (p4 ∧ ((p1 → False) ∧ (p4 → (True ∧ False))))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h12
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248572977888431300372620542751 : ((p3 ∨ False) ∨ ((((p1 → p4) → ((p5 ∧ (p1 ∧ False)) ∨ (p4 ∧ (((True ∨ p2) → p1) → (p3 ∨ p1))))) ∨ (p2 ∨ True)) ∨ (p4 ∧ False))) := by
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
theorem thm_5_vars_206061910777125795312414042132 : ((p3 ∧ (((p2 ∧ True) ∨ p4) ∨ p5)) ∨ (((p2 ∨ p4) → False) → ((((p2 ∧ ((p3 ∨ p3) ∨ p1)) ∧ p4) ∨ p3) ∨ (True → (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48133567405139491339008164962 : (((((p1 ∧ p5) ∨ True) ∨ (p5 → (((p2 → ((p4 ∧ False) ∨ p1)) → True) ∧ (((False ∨ p2) → p5) ∧ (p2 → p1))))) → (p2 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113037411805657474564262569771 : (((False ∨ (((False ∧ ((p1 ∧ (p4 ∨ p2)) ∨ (p4 ∨ p5))) → (p3 ∧ p3)) ∨ ((p5 ∨ ((False ∧ p2) → False)) ∨ p5))) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807097848603772743569015764090 : (((p4 → (((False ∧ ((((p4 → p2) ∧ p3) ∨ p4) → p4)) ∨ (True → (((p2 ∧ p1) ∨ False) ∧ p3))) ∨ (False ∨ ((p1 ∨ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259094145280565830034522326106 : ((True → p5) → ((p2 ∧ (p1 ∧ (p5 → (p2 ∨ p2)))) ∨ ((((p4 ∨ p3) ∨ ((p3 ∧ p5) ∧ True)) ∨ (p2 ∧ p3)) → ((p3 → p3) ∨ p5)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608672782723449668694373688631 : ((((((p1 ∧ ((False → (((True ∧ ((((p4 ∧ p1) → (p5 ∨ True)) → p2) → False)) ∨ p1) → p4)) → p1)) ∨ (p1 ∨ p3)) ∨ True) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_779770538122147631723353468205 : (((p2 ∨ (((p3 ∨ ((((False ∧ p1) → True) → (p5 ∧ p3)) ∨ p2)) ∨ (p5 ∧ (True ∧ (p2 ∨ (p2 ∧ (p1 ∧ (p2 ∧ p1))))))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232673296481829586342243845949 : ((p1 ∧ (p3 ∧ p4)) → ((p1 → p4) → (((True ∧ ((True → True) → (p4 → p5))) ∧ True) → (((p4 → p5) → False) ∨ (p2 → (p4 ∨ p2)))))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201116435248948352818620895641 : ((True → ((p2 → True) → ((p1 ∨ True) → False))) → (p3 ∨ (p2 → (((p1 ∧ p2) → (((((p3 → True) ∨ p4) ∨ True) ∨ p4) → p3)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686945365789735410771068806094 : ((((p2 ∨ ((((False ∧ p4) ∨ ((p5 ∧ (True ∨ (p5 ∨ (p1 → p1)))) → p5)) → p5) → False)) → ((p3 → (True → (p2 → p5))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91115484532806409188792650899 : (((p4 → False) ∧ ((p4 ∨ ((p5 → (False ∧ ((((p5 ∧ True) ∨ (((p2 ∨ (p4 ∨ False)) ∨ False) ∨ p3)) ∨ p3) → p5))) ∨ p2)) ∧ p4)) → p2) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37170093406835142612003681242 : ((((((p1 ∨ (True ∨ (p2 ∨ p5))) ∧ (True → ((p5 ∨ False) ∧ (p5 ∧ p2)))) ∨ (((False ∧ p1) ∨ p2) ∨ (p3 ∧ p1))) ∧ p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114766682735964708328847330391 : (((p2 → (p5 ∨ (p3 ∧ ((p5 ∨ (((p1 ∧ False) ∧ False) ∨ p2)) ∧ (p1 ∨ p1))))) → (((True → (p3 → p4)) ∨ p3) ∨ False)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700103349738707736770610538485 : (((((True ∧ (p1 → p4)) → (p4 ∧ (p2 ∨ ((p5 ∨ p4) → False)))) → ((p1 ∨ (p5 ∧ ((False ∧ p1) ∧ p3))) → (p5 ∨ (p5 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146954791770067707039993250466 : ((((False ∧ (((p5 ∨ (p5 ∨ p5)) ∧ True) ∧ ((((p2 ∧ (p1 ∧ p2)) ∨ p1) → p1) ∧ p5))) ∨ p4) ∧ p4) ∨ ((p5 → (p4 → p5)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749919854768261143544691371482 : (((True ∧ (((p2 ∧ ((p1 ∨ ((p2 → p5) ∧ (p5 ∨ True))) ∧ (p5 ∧ (((p2 ∧ p3) ∧ p3) ∧ (True ∧ (p2 ∨ p3)))))) ∨ p4) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319131000036310357264433721445 : (p4 ∨ (((((p3 ∧ p2) ∨ (p1 ∨ (((p1 ∧ p3) ∨ p1) ∧ p4))) ∧ True) ∨ ((False ∧ p2) ∨ True)) ∧ (p5 → ((p4 → False) → (p4 → p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68340308268667544484430628349 : ((p3 → (((p1 ∨ False) ∧ ((((p4 → p1) → (False ∨ True)) → p5) ∧ p1)) ∨ ((p5 → False) → (p4 ∧ ((p2 ∨ p2) ∨ (True ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780169919871169420262630558283 : (((p2 ∨ (((p2 → True) → ((p1 ∧ p1) → ((True ∧ ((p4 ∨ p2) ∨ p5)) → ((p4 → (p5 ∨ p3)) ∨ p5)))) ∧ (p2 ∧ (p4 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712666250085302481647769410313 : (((((False ∨ p5) ∧ (p4 → (False ∧ False))) ∨ (((((p2 → p2) ∧ ((((False ∨ p5) → p4) → p4) → p2)) ∨ (p5 ∧ p5)) ∧ p5) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649484003637014355544138048484 : (((((((p4 → True) ∨ (p2 → p1)) → ((False ∧ (p1 ∨ (True ∧ True))) ∧ (p5 → (p2 ∨ (p1 → p5))))) ∧ (True ∨ p3)) ∧ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217844031137966336848689995781 : (((p5 ∨ (True ∨ p5)) → p2) → (False ∨ (p5 ∨ (p1 → ((p2 → (p1 ∨ (p3 ∧ p3))) → ((((p1 → p5) ∧ True) → p3) → (p2 → p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699619446516109244395731246086 : ((((((((False → True) ∨ p1) ∧ (False ∨ False)) → (False → p4)) → True) → (((False → (True ∨ p4)) → p3) ∧ (p2 → ((p4 ∨ True) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642723571036734413161924177462 : ((((p1 ∧ ((p3 → p1) ∧ (((p2 ∧ (p1 ∨ (p2 ∧ ((((True → p4) ∨ (p2 → p2)) ∧ False) ∨ (p1 ∧ True))))) ∧ True) ∨ p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762219631043550866943254074990 : (((p3 ∧ ((((p4 ∧ p2) → (p5 ∧ (((False ∨ p4) ∧ ((False ∧ ((p5 → p4) → p5)) ∧ p4)) ∨ (p2 ∨ p4)))) ∨ p3) → (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314239581096424207564861432438 : (p3 ∨ ((((((True ∨ ((p4 ∨ ((((p5 ∧ p2) ∧ p5) ∧ False) ∧ p4)) ∧ False)) ∨ p2) → p5) ∧ p5) ∧ (p2 ∨ p3)) ∨ (p1 ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_766291323383982929341966574417 : (((p4 ∧ ((p3 ∧ p3) → ((False → p5) ∧ (((((p3 ∧ (p5 ∧ p4)) ∨ True) → (p3 ∨ (True ∨ (False ∨ p5)))) → (p4 ∧ p1)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611203511311978370328351141991 : ((((((p5 ∨ (p1 ∨ p1)) → ((((p3 → p5) ∧ (((((p1 ∨ p5) → p3) → False) ∧ p2) ∨ p2)) → p1) ∨ (True ∨ p1))) → p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115049265749215195754666938937 : (((((p4 ∨ (True ∧ (p5 → p1))) ∧ (p2 ∨ (p3 ∧ True))) → p5) ∨ (p1 → ((p5 → p3) → (((p5 ∨ p1) ∧ p1) ∨ p3)))) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694082157360297064437835501759 : ((((((p3 ∨ p2) ∨ ((p2 → (p2 ∧ p4)) → p2)) ∨ ((p5 ∧ p4) → True)) ∨ ((((True ∧ p4) → False) ∨ p2) ∧ (p4 → (True ∧ p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117683352910378109965255927047 : ((p3 ∧ ((p3 → ((p4 → False) ∨ p3)) ∧ (((((False ∧ (p2 ∨ (p4 ∧ p5))) ∧ True) ∧ p1) ∧ ((p3 ∧ p3) ∨ p4)) ∨ p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41647402420136825570213305224 : (((((p2 ∧ ((p5 → p2) → p2)) → p4) ∧ (p4 ∧ (((p4 → (p1 ∧ ((p2 → (p1 ∨ p5)) ∨ p3))) ∨ p2) → (p2 ∧ p5)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264059300247290993119627747557 : (True ∧ (((p1 ∧ (p2 ∨ (((False ∧ p1) ∧ False) ∧ p3))) ∧ p2) ∨ ((False ∨ ((True → p4) ∨ ((p3 → (p3 → p2)) → p1))) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_586468010403244623084846104816 : (((((((False ∧ p1) ∨ p1) ∨ ((((((False → p4) → p2) ∨ (p1 ∨ p4)) ∨ (p2 → (True → p2))) ∧ (p1 ∨ False)) → p2)) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196944733250705186780410909672 : (((((False ∨ (False ∧ p1)) ∨ p1) ∨ p2) ∨ p1) ∨ ((p1 ∨ ((p1 ∨ (p4 → ((p1 ∨ (p1 ∧ (False → (p4 ∧ True)))) ∧ p1))) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36795214950815984008299426018 : ((p5 → (((((p5 → p5) → (((p3 ∨ (p2 ∨ True)) → p2) → ((p3 ∧ p3) → p1))) → p2) ∧ p2) ∨ ((p2 ∧ p4) → (p2 → p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58160366806764297786149534158 : (((p3 ∧ True) ∧ (((p4 → (p4 ∧ p2)) ∨ ((p5 ∧ p3) ∨ ((p5 ∧ p1) ∨ p4))) → ((False ∧ (p4 → ((p4 ∧ p2) ∧ p3))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113930441248850414516703859909 : ((((p1 ∨ ((((False ∧ False) ∨ p3) ∧ (p4 ∨ p2)) ∧ p5)) ∧ (p4 ∧ (True ∨ ((p3 → p3) → True)))) ∧ ((True → p4) → True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156871395398957355305683955428 : ((((False ∧ ((p2 ∨ (p5 → ((((True ∨ p3) ∧ True) ∧ p5) → p2))) ∧ (p2 ∨ p1))) ∧ p5) ∨ p1) ∨ (p3 → (p3 ∨ ((False ∨ p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168309805186182849751084147453 : (((p5 ∨ False) ∧ (((p4 → p5) → (((False ∨ (p3 → p3)) ∧ p4) ∧ (p3 ∧ False))) ∨ False)) → ((((p4 → p2) ∨ (p3 ∧ True)) → p4) → p2)) := by
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
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63256426166769244495786317184 : ((p5 ∧ (((p4 → (p1 ∨ ((False ∨ False) ∨ p2))) → p5) ∨ (p5 → (((False ∧ p2) ∧ (((p5 ∨ False) ∧ p1) ∧ False)) → (p5 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213906297291985690716072795347 : (((p5 ∨ (False ∧ p5)) ∨ p5) ∨ ((True ∧ (((p4 ∨ False) ∨ (p3 ∨ ((p1 ∧ True) ∨ (((p1 ∧ p3) ∨ (p1 ∨ False)) → True)))) ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744283806391899258872947764085 : ((((p1 ∧ p3) → (p3 → ((p4 ∨ ((p1 ∨ p1) → (False ∧ p4))) → (p4 ∨ ((p1 → False) ∧ ((p5 → ((False ∧ p5) ∨ False)) ∧ p2)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304385528545916136053839890691 : (p1 ∨ ((((p5 → True) ∧ True) ∧ ((True ∧ ((((((((True → p3) → p2) → False) ∨ (p2 ∨ p1)) → p1) ∨ True) ∨ p1) ∨ p3)) → False)) → p2)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ ((((((((True → p3) → p2) → False) ∨ (p2 ∨ p1)) → p1) ∨ True) ∨ p1) ∨ p3)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113615294285750123373496470673 : (((p5 ∨ ((((True → (p1 ∧ p2)) → False) ∨ p4) → (((p3 → True) ∨ (p3 ∧ (p1 ∧ p2))) → (p4 ∧ False)))) ∨ (True ∨ p5)) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55088498060776848419517851127 : (((p1 → (p3 ∨ (False ∧ (p2 ∨ True)))) ∧ ((p5 → p3) ∧ (((False → ((((True ∧ p4) ∧ False) → p3) ∧ p5)) ∧ p5) → (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67959784283642846584423079669 : ((p2 → (((p3 ∧ p3) ∨ (p1 → True)) → ((((True → False) ∧ ((((p1 → p5) ∧ False) ∧ p2) ∧ p4)) ∨ (True ∧ p3)) ∨ (True → True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337870060252225166367807241696 : (p1 → ((p1 ∧ ((p2 ∧ ((False → (p4 ∨ p3)) ∧ p5)) ∧ (p4 ∧ (p3 ∨ p5)))) ∨ (((False ∧ False) → p2) ∧ (p5 → (p5 ∨ (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178911586337636995366324727597 : (((True → False) ∧ ((((p5 ∨ p5) ∧ p4) ∧ (False ∨ p3)) ∨ (p5 ∨ p4))) ∨ ((False ∧ (p5 → ((p3 → p2) ∨ False))) → (p1 ∧ (p3 ∧ p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136882708524957033998393718704 : (((p2 ∨ False) ∨ ((((p3 ∧ (((p5 ∧ True) → False) ∨ p4)) ∨ p1) → (p2 ∨ (p4 → (p2 → p3)))) ∨ (True ∨ True))) ∨ ((False ∧ True) ∨ p5)) := by
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
theorem thm_5_vars_158967264250149020550532129550 : ((p3 ∨ (((False ∨ p5) ∨ ((((p5 → p4) ∧ p3) ∨ p5) → (p3 ∨ (p4 ∨ (p4 ∨ p1))))) ∧ p3)) ∨ (False → (p5 ∨ (p2 → (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207357583183460463675462065701 : ((((True ∨ True) → (True → p3)) ∨ p4) → ((((p4 ∧ ((((False ∨ p5) ∨ p3) ∨ p1) ∧ ((p4 ∨ p2) ∨ p3))) → (p4 ∧ p5)) ∨ True) ∨ False)) := by
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
theorem thm_5_vars_321077012864326193267414339273 : (p4 ∨ (p1 ∨ ((p2 → ((p4 → (p4 → True)) ∧ p1)) → ((((((False ∧ (p3 ∧ False)) ∧ (p4 ∧ False)) ∨ True) ∧ True) ∨ p2) ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118518617936363959789591335758 : ((p3 ∨ ((p3 ∧ p3) ∧ ((p2 ∨ ((p3 ∨ ((p1 → p4) → True)) ∨ ((p3 → ((True ∨ p4) ∧ p5)) ∧ p1))) ∨ (False ∨ p2)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781092554810409484356212723266 : (((p2 ∨ ((p3 ∧ p2) ∨ (True → (((p2 ∧ p3) ∨ (p1 ∧ (((p4 → (False ∨ p1)) → (p2 ∧ p2)) → (p3 → p1)))) ∧ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774995160478215591146948180493 : (((False ∨ ((p4 ∨ (p4 → p2)) ∨ ((((p2 ∧ ((True → p4) → p5)) ∨ (((p2 → p5) ∧ (p1 ∨ (p5 → True))) ∧ p3)) ∧ p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253863201741364452614571999207 : ((p1 ∧ p3) → (((p1 ∧ (p1 → (((p1 ∧ ((True ∨ (p3 ∨ p2)) ∧ (p1 → p5))) ∨ p4) ∧ p4))) → True) → (((p4 → p5) ∧ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112834471741698186678568262030 : (((((p1 ∨ (p5 ∨ p2)) ∨ True) → (((p3 → (True → (((False ∧ (p2 ∧ p3)) ∧ p2) ∨ (p2 → p1)))) ∧ p5) ∧ p2)) → p5) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p5 ∨ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113368694348513552619180747079 : (((False ∨ ((p2 ∨ p2) ∨ ((p4 ∧ (((p2 ∧ False) → ((p1 ∧ p3) → p1)) ∨ p5)) → (False → (p3 ∨ True))))) ∧ (p5 ∧ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55587944638202211995767690945 : (((p3 ∨ ((p5 → p2) ∧ (False ∨ p1))) → ((True ∧ ((False → p2) ∧ (False ∨ p5))) → ((p1 ∨ (((p2 → False) ∧ False) ∧ p1)) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43528734128529216413994287105 : ((((False → ((p4 → (p5 → p3)) ∨ (p2 → (((((((p2 → p1) ∧ (p2 ∨ True)) ∨ p2) → False) ∨ True) → True) → p2)))) ∨ p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159374577415703698317082100709 : (((((((((False → p3) ∨ p2) ∨ False) ∧ (p1 ∧ p1)) → p1) → (p1 ∨ (p2 → p1))) ∨ p1) ∧ p2) → ((p5 ∨ p1) ∨ (True ∧ (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((((False → p3) ∨ p2) ∨ False) ∧ (p1 ∧ p1)) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h8.left
          let h12 := h8.right
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h8.left
          let h15 := h8.right
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h5
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43057245555593302094230031555 : ((((((((p2 ∨ p4) ∧ p1) → (((p2 ∧ ((p4 ∨ p1) ∨ p5)) → (p1 ∨ p5)) ∨ (True ∨ p3))) ∨ (p2 ∨ False)) → p5) ∧ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190931037226135655329172349338 : (((((False → p5) ∨ p3) → p3) ∧ ((False → p4) → p5)) ∨ (True ∨ (False ∨ (False ∨ ((((p2 ∧ (p4 ∧ p1)) ∧ (False → p3)) ∨ p1) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619601994525647071165064835298 : (((((p1 ∧ p2) ∧ ((((((p3 ∧ True) → True) → p1) ∧ ((False → (((p2 → p4) ∧ p3) ∧ (True → p2))) ∨ p5)) ∧ True) ∨ True)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209129114979966821723600591551 : ((p3 ∨ (((False ∨ True) ∧ p2) ∧ True)) → ((((p3 ∧ p3) → p3) → ((p4 ∨ p5) ∨ p1)) ∨ ((p5 ∧ p4) → (p4 ∨ (False → (False ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622343500700906145149290851528 : ((((p3 ∧ (((p4 ∨ p3) ∨ ((((p3 ∨ (True ∧ p3)) → (p5 ∨ ((True → p4) → False))) ∨ (True ∨ p2)) ∨ False)) ∧ (p3 ∨ False))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_218282367141797401548371326577 : (((p3 ∨ False) ∨ (True ∧ p5)) → (p4 ∨ (((p4 ∨ p1) ∧ (True → (((True ∧ (((False ∧ p3) ∧ True) → False)) ∧ p3) ∧ p2))) ∨ (True ∨ p5)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200698806171832597218690282851 : ((p2 ∧ (((True ∧ False) ∨ False) → (False ∨ p4))) → ((((p1 ∨ ((p5 ∧ ((p5 → p4) → (False ∨ True))) → (p1 → False))) ∨ p2) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∨ ((p5 ∧ ((p5 → p4) → (False ∨ True))) → (p1 → False))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178907245081167154574839753169 : (((p4 ∨ p4) ∧ ((((p2 ∧ (p2 ∧ (p3 ∨ p5))) ∨ p2) → p5) → p2)) ∨ ((False ∧ (p5 ∧ (((False → p2) → p3) ∨ p4))) → (p3 ∨ p1))) := by
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
theorem thm_5_vars_57343125655393310304052414092 : (((p2 ∧ (False ∨ True)) ∨ ((p3 ∧ ((p4 → ((((p2 → False) ∧ ((p3 → p5) → p5)) ∨ p5) ∨ (p2 → (p3 ∨ p1)))) → p1)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41803075575024796911854613349 : ((((p3 ∨ (p2 ∨ (p4 ∧ p4))) → (((p1 ∧ p3) ∧ (p1 ∧ p4)) ∧ (p5 ∨ (((p5 ∨ ((False ∨ p4) ∨ p1)) ∧ p1) ∨ p4)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137015378132705402994086955238 : (((p2 ∨ p2) → (((True ∨ (False ∧ (((p3 ∨ (p4 ∧ p4)) ∨ p3) → True))) ∨ (False → True)) → ((True → False) → p4))) ∨ ((p4 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57095776070635290809886071062 : ((((p4 ∧ p4) ∧ p4) ∨ ((False ∧ ((True → ((p4 ∧ p2) ∧ p5)) ∧ (p3 → (False ∨ ((True ∧ (True ∧ (p1 → True))) ∧ p1))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137980573588379687515532666939 : ((p5 ∨ (((True ∧ False) ∧ p1) ∨ (p5 ∨ (((p4 ∧ p4) ∧ (p2 ∨ (((False → p4) ∨ False) ∨ p3))) ∨ (p1 → p4))))) ∨ ((True ∨ True) ∧ True)) := by
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
theorem thm_5_vars_63382649271204000656738832285 : ((p5 ∧ (False ∨ ((((((((p1 ∨ False) ∧ (p2 → p3)) ∧ ((p2 → p1) ∧ True)) → p5) ∧ (p3 ∧ (p1 ∧ True))) ∨ False) ∧ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323492325900150135566267833246 : (p5 ∨ ((((((False ∧ p5) → ((p5 → False) → p3)) → ((p1 → p2) ∨ False)) ∧ (p1 ∧ p5)) ∨ (False ∨ (p2 ∧ True))) ∨ (p3 → (False ∨ p3)))) := by
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
theorem thm_5_vars_204653664616865575361220716200 : (((p3 ∧ (p4 ∧ (False ∨ False))) ∨ False) ∨ ((False → p3) ∨ ((p5 ∨ (True ∧ True)) ∧ ((((p2 → False) ∧ p2) ∧ (p4 ∧ True)) ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675973076499621463224211335569 : ((((((p5 → (p2 ∧ ((p1 ∨ True) ∧ True))) → p5) ∧ (p2 → (((p3 ∨ p4) ∨ p3) ∧ (False ∨ p1)))) ∧ (((p2 ∧ False) → False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475977696872383559262571614529 : ((((((((p1 ∨ p5) ∧ p4) → (True → p3)) ∨ p4) → p3) ∨ ((True ∧ (((p3 → p4) ∨ p5) ∨ True)) ∨ (((p2 ∧ True) ∨ False) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



