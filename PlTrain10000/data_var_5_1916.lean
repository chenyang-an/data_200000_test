variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729722471487669678512721412962 : (((((p2 → p4) ∨ p3) → ((((p1 ∨ p2) → (p4 ∨ (p4 → (p4 ∨ (p2 ∧ (p1 ∧ True)))))) ∨ (True ∧ p5)) → (p4 ∨ (False ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303044020946968479786404800094 : (False ∨ (p2 → (((p3 ∨ ((p5 ∧ (False ∧ True)) ∨ ((((p3 ∧ True) ∧ True) ∧ p1) ∧ ((False ∨ p4) → p2)))) → ((p4 ∨ False) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165165877138114902755959565158 : ((((p2 ∨ p1) ∨ (p4 ∧ (p2 ∧ (((True → p1) ∨ False) → (p3 ∨ p1))))) ∧ (p3 ∨ p1)) ∨ (True ∨ ((p1 ∧ ((p3 ∧ p1) ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343244926412467030136506195840 : (p2 → ((p5 ∨ (False ∨ p1)) → ((False ∨ (((p3 ∧ p3) ∧ ((p5 ∨ p4) ∨ (p4 ∧ (p2 ∧ p3)))) → (((p3 ∨ p5) → p5) ∧ False))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167206682028041865448469692788 : (((True ∨ ((p1 ∧ (p3 ∨ ((p1 ∧ False) ∧ False))) ∨ ((True ∨ p5) ∧ (True ∨ p1)))) ∨ p3) → ((p3 ∨ (True ∨ ((p4 ∧ p1) → p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111915917705767199929225287578 : (((((p2 ∧ ((p2 ∨ p3) ∧ p3)) ∧ ((p1 → p5) → (p3 ∧ p5))) ∨ (p2 → ((p5 ∨ (p1 → p3)) ∧ (p2 → p5)))) ∨ p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57602532200747313824758590874 : ((((p2 → p4) ∧ p1) → ((False ∨ (((((p3 → False) ∧ ((p2 ∨ p5) ∧ p1)) ∨ ((p2 → p5) → p5)) ∨ False) ∨ (p4 ∨ p1))) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316567816688877412798508887379 : (p3 ∨ (p3 ∨ ((((((p2 → (p1 ∨ p3)) ∨ False) ∧ True) ∨ False) ∨ (p1 ∨ ((p1 → True) ∨ True))) ∨ (((p3 ∧ (p5 ∨ p4)) → True) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36633669289921780039520729382 : ((p5 → (((p2 ∧ (p1 ∨ ((False ∨ ((p5 ∧ True) ∧ ((p4 ∨ True) → (p1 ∧ ((False ∧ p3) ∧ p4))))) ∧ p5))) ∨ (p5 → True)) ∧ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609999515355974798785822381129 : ((((((((p4 → (True → (p1 ∧ True))) → (((p2 ∨ (p3 → ((True → p4) ∧ (True ∧ p4)))) → p4) ∧ True)) ∨ p5) ∧ p4) → p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_168972668649581153644639662044 : ((False → (((True → (p3 → p4)) ∧ p4) ∨ ((False ∨ ((p3 → False) ∧ p5)) ∨ (p5 ∨ True)))) → (((p4 → (p1 ∧ (p3 ∨ p5))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388864604500911456870124546780 : (((((True ∧ (((p5 ∧ True) → (p1 ∨ (False ∨ (False ∧ p3)))) → ((True ∧ p2) ∧ p5))) ∨ (p1 ∧ (((p4 ∧ p2) → p1) → p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_68589751866314121776376191894 : ((p4 → ((False ∨ ((p2 → ((True → p3) ∨ (p5 ∧ (False ∧ (((p4 → p5) ∧ (False ∧ (p3 ∨ False))) ∧ p3))))) ∨ (p1 → True))) ∧ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218895857455134378283766103137 : ((p3 ∧ ((p2 → True) ∧ p3)) → (((((p5 → p2) ∨ (((True → (p2 ∨ False)) ∧ p2) ∨ False)) ∨ p3) ∧ ((p4 → True) ∧ (False ∧ p5))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136176584732574291319419172643 : (((((True → p1) → (p5 → p4)) ∨ p5) ∧ (p3 ∧ ((p5 ∨ (((p3 ∨ (True ∨ p3)) → (p3 → False)) ∨ p5)) ∧ False))) ∨ ((False ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780991441361564023714438131271 : (((p2 ∨ ((True → (False ∧ True)) → (((p2 ∨ (True ∧ p4)) ∧ ((False ∨ ((p5 ∨ ((False → p1) ∨ p1)) ∨ p3)) ∧ (False ∧ p5))) ∨ p3))) ∨ False) ∧ True) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172481794318241419483805269457 : ((((p3 ∨ p5) ∧ (p2 ∨ p2)) → (((((False ∨ p4) ∨ p2) → p5) → p5) ∨ p4)) ∨ (((((p5 ∧ p4) ∧ p5) ∨ (False ∧ p5)) ∨ p2) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((False ∨ p4) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((False ∨ p4) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247946344435468372303963995448 : ((p1 ∨ p3) ∨ (p5 → (((p1 ∨ p1) ∧ (p3 ∧ (p4 ∧ (True → p3)))) → ((((p2 ∨ p2) ∨ (p2 ∧ False)) ∧ p2) ∨ ((p3 ∨ p4) ∨ p1))))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50282563185087153064076438431 : ((((((p5 ∨ p4) → (((p3 → p4) ∧ (False ∨ (p3 ∨ (p2 ∧ p3)))) ∨ p2)) → True) → (False ∧ p5)) ∨ ((p5 → p2) → (False → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45731169550465526635658970204 : (((True → (p1 ∨ (p2 ∨ (p1 ∨ ((p2 ∨ ((p3 ∧ ((False → p5) → True)) → (p2 ∧ (True → (False → (p2 → False)))))) ∨ p3))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54566660049266553093163787585 : (((p5 ∧ (p2 ∧ (((p5 ∨ p4) → p5) ∧ p2))) ∨ (p3 ∨ (p3 → ((p1 ∧ p1) → ((p5 → (False → ((p2 ∧ p3) → p2))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149376291979428931721914851671 : (((p2 → p3) → ((p5 ∧ ((((p1 ∧ p2) ∨ False) ∨ p1) → ((p3 ∧ ((p3 ∨ p3) → p3)) → p5))) ∨ True)) ∨ ((False → p1) → (p3 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64244079531229834068215159553 : ((False ∨ (p1 ∨ (p5 → ((False ∧ p3) ∨ ((((True → (p5 ∨ p5)) ∧ (True ∧ ((True ∨ p5) ∨ p3))) → (False ∨ False)) ∧ (p1 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327863741265553369278330356981 : (True → (((p1 ∧ p2) ∧ ((((((((True ∧ (p1 → True)) ∨ p2) ∨ (False → p4)) ∧ False) ∧ p3) ∧ p2) → (p1 → p4)) → p1)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246296700858816239285774592570 : ((p4 ∧ p4) ∨ (False ∨ (((p4 ∧ p3) ∨ (p2 ∧ ((False ∨ (((p2 → p5) ∨ False) → p2)) ∧ (p1 → ((p2 ∨ p3) → (p5 ∨ False)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_559639803354274416410206305 : (((p2 ∨ ((p2 ∧ (((p5 → (True → ((True ∧ (p3 → (p4 → p1))) ∨ (p4 ∨ p4)))) → p4) → (p3 ∧ p5))) ∧ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255520216863643380739760459352 : ((p5 ∧ p2) → ((p1 ∨ p4) → ((p3 ∧ ((True → (True → (False → ((True → ((p5 → (True ∨ (p5 ∧ False))) ∧ p3)) → p3)))) → p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90918377361120176625705003219 : (((True → False) ∧ (((((p5 ∧ (p5 ∨ p2)) ∧ (p4 → (((p4 ∧ p4) → (p5 ∨ True)) ∨ (p4 → p2)))) ∨ p2) ∨ (False → True)) ∧ True)) → p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611558583922465175946998302618 : (((((True ∨ ((p3 ∧ p1) ∨ ((p3 ∧ ((False ∧ (p3 → (((p1 ∨ (p5 ∧ p3)) → p1) ∧ (p4 ∨ p1)))) ∧ p3)) → p5))) → p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_310856793494489108340557303601 : (p2 ∨ (((p2 ∨ True) → p4) → (p4 ∧ (((p1 ∨ (True ∧ (p3 → p4))) → False) → (((True ∧ (p4 → p3)) → ((p1 → p3) → p2)) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : (p1 ∨ (True ∧ (p3 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h9
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h14 : (p1 ∨ (True ∧ (p3 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h18 := h4 h14
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180620800605977831109242048768 : (((p4 ∧ (True → ((p3 ∧ p2) ∧ True))) ∧ (False ∨ ((p2 ∨ p4) → p3))) → (p1 ∨ (((False ∨ (p2 ∧ (p3 ∨ p4))) ∨ p3) ∧ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383246377238088047694491105863 : (((((p5 ∨ (((((False → p1) ∨ ((((False → p3) → p2) ∧ True) → p3)) ∨ (p1 ∨ (p4 → True))) ∨ p2) → (True ∧ p2))) ∨ True) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614014581976570131540784142619 : ((((((p5 → (True → p4)) ∨ (p3 ∧ (((p4 ∨ (p4 ∨ False)) ∧ (p2 ∧ (p5 ∧ False))) ∧ (p2 → p2)))) ∨ ((True ∨ p1) ∧ p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213158527575405840631977882493 : ((((p2 ∧ p4) ∨ False) ∧ False) ∨ (p4 ∨ (((((False → p1) ∧ p5) ∧ ((True ∧ p4) → (((True → False) → (p3 → p4)) ∨ p1))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244299847148015067324175760409 : ((False ∧ True) ∨ (p2 → (((p1 → (p5 → False)) ∨ ((p2 ∧ (p5 → p2)) ∧ ((p5 → p4) → ((p3 ∨ ((True ∨ p1) → p3)) → p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51706547757667100657808689184 : ((((True → (p3 → (p2 ∨ (p5 ∧ ((p4 ∧ p5) ∧ p1))))) → (True ∧ (p1 ∧ p3))) ∧ (p3 ∧ ((p4 → ((p5 → p1) → p2)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259312138607239675954413910318 : ((False → p2) → (((p1 → (p2 ∨ (p2 → p4))) → ((((p3 ∧ p2) ∧ p1) ∨ ((True ∨ (p2 → (True ∨ p1))) → p3)) ∨ (p1 → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134415452234862413191093692903 : (((p2 → (False ∧ (p2 → ((p3 ∧ ((((True ∨ True) → (True → p3)) ∧ (p5 ∨ p1)) → p4)) ∧ (p5 ∨ p3))))) ∨ False) ∨ ((False ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112809416348841408296456350315 : (((((p2 ∨ (p1 → (p2 ∧ p2))) → p3) → (p3 ∧ (True ∨ ((p5 → (True ∧ (False → p4))) ∧ (p4 → (p5 ∨ p2)))))) → p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116263676167051833789811428014 : (((p2 ∧ (p2 ∨ p3)) ∨ (True → (((p4 ∨ (p3 ∨ p2)) ∨ (((False ∧ False) ∧ (True ∨ (p4 ∨ (p5 ∧ p3)))) ∧ p4)) ∧ True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37976682259936978791525148946 : ((((((True ∨ ((p3 ∧ (True → p2)) → p1)) ∧ ((((p2 → (False ∨ p2)) → p4) ∨ p2) ∨ p4)) → (p2 → p2)) ∨ (p5 → True)) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720239991228881743242966765128 : (((((p3 → (p4 ∧ p1)) ∧ True) → (((True ∨ p1) → ((False ∨ ((p3 → (p5 ∧ p3)) ∧ p1)) ∨ (False → p3))) ∧ ((p3 ∧ p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175325783001500096177379888611 : ((p4 ∨ ((p2 → False) ∧ (((((p1 → p4) → p2) → (p5 ∧ True)) ∧ p4) → p2))) → (p4 → ((p4 → (((True ∨ p5) ∧ False) ∧ p2)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340091921522838792325823165967 : (p1 → (p3 → ((p5 ∨ ((p5 ∨ (((True ∨ p3) ∨ p2) → (p2 ∧ (((p5 ∧ p5) → p5) → p4)))) ∨ (((p4 → p4) ∧ False) ∧ p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117610660098964503096627884855 : ((p2 ∧ (p2 → (False ∨ (((((p5 → True) ∨ ((True → (False ∨ ((p4 ∧ p3) → p2))) → p4)) → (False ∧ p5)) ∧ p2) ∨ False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310674908252121769309791120633 : (p2 ∨ (((p2 → p4) ∨ (p5 ∨ p3)) → ((p5 ∨ p5) ∨ (((p4 ∧ ((False ∧ p3) ∧ (True ∧ True))) ∧ (p3 ∧ p2)) → (p3 → (True → True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697699460959243381831364199909 : ((((True → ((True ∧ p3) → (p3 → (((p3 ∧ p2) → p1) ∧ p5)))) ∧ (p5 ∨ (((((p4 → False) → p5) ∧ False) ∧ (p5 → False)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158292710138182402243585751487 : ((((p1 ∨ p1) ∨ p1) → (p4 ∨ (((False → ((p4 ∨ p2) ∨ p5)) → (p5 → (p5 ∧ p2))) ∨ True))) ∨ ((False ∧ ((p3 → p3) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340849159128319966604914359219 : (p2 → (((((p4 → (True ∨ True)) → (False ∧ p5)) ∧ (((False → False) → (p4 ∧ (p2 ∧ p3))) ∨ (p2 ∧ p1))) ∨ (False ∨ (p2 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192699565286348081872219423210 : (((((False → (p3 ∨ p1)) → p2) → (p5 ∧ p5)) → p5) → (((((p4 ∧ True) → False) → (False ∧ (p1 ∨ p5))) → p3) ∨ (True ∨ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116096462321795577299566924308 : ((((p2 → p2) ∨ p1) ∧ (((((p2 ∨ ((p2 ∨ True) → (p4 ∨ (p3 → p1)))) ∨ (p3 → p4)) → (p3 ∧ p4)) ∨ p3) → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215774345373390349896132078586 : ((p1 ∨ ((p4 ∨ p1) → p2)) ∨ (((((p1 → False) → p1) ∧ p2) ∧ p1) → ((((p2 → (p5 ∧ ((p3 ∨ False) ∨ p3))) ∧ p4) → p5) ∧ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197980999372620428565788666008 : (((p2 ∨ p2) ∧ (((False → p1) ∧ p5) → p2)) ∨ (((p1 ∨ (((p2 ∨ p5) ∧ ((p3 → False) ∧ (p5 ∨ p4))) ∨ (p2 → p2))) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (((p2 ∨ p5) ∧ ((p3 → False) ∧ (p5 ∨ p4))) ∨ (p2 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259069583092971652581128163936 : ((True → p5) → (((True → p4) ∧ ((p1 ∨ (((((p4 → p1) → (p5 ∧ p3)) ∧ p3) → (p2 → True)) → ((p1 ∧ p3) ∨ p1))) ∧ p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321572213904353558950835428148 : (p4 ∨ (p2 → (True ∧ (((p1 → (((((p4 → p1) → False) ∨ False) ∧ (p1 ∧ (p3 ∧ p1))) ∨ (p5 → True))) ∨ (p1 ∧ (False → p3))) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172090913888913339411701489515 : ((((p1 ∨ p5) → ((p4 ∧ (((p2 ∨ p4) ∧ p5) ∧ True)) ∧ p4)) → (False ∧ p3)) ∨ (True ∨ ((((p4 ∨ False) ∧ p5) ∨ (False ∨ False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153030117580112505127896261732 : ((p2 ∧ (((p5 ∨ (p3 ∧ p3)) ∨ False) → ((p2 ∨ (p4 → p5)) ∧ (p1 ∧ (True ∧ (p5 ∧ (p3 ∨ p4))))))) → (((p1 ∧ p3) ∧ p1) → p5)) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p5 ∨ (p3 ∧ p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135981226998049796347756723325 : (((((p5 ∧ p2) → ((True ∨ p1) ∨ (p4 ∨ p4))) → False) ∨ (True ∨ ((((p2 ∨ True) ∨ (p3 ∧ True)) → p1) → False))) ∨ ((p3 ∨ p4) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636345371617607527524582200386 : ((((((p3 ∨ ((True → ((p4 ∨ p4) ∨ (p1 ∨ p2))) ∨ True)) ∧ ((p3 ∨ p1) ∨ True)) → (p3 ∨ ((p2 → (p2 ∨ p5)) ∧ p3))) → p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((True → ((p4 ∨ p4) ∨ (p1 ∨ p2))) ∨ True)) ∧ ((p3 ∨ p1) ∨ True)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41237097582726553293004393174 : ((((p2 ∨ (((p2 ∨ (p2 ∧ (p2 ∨ p2))) ∨ (True ∧ ((p1 ∧ p2) ∨ p5))) ∧ (p3 ∧ p2))) ∧ ((False ∧ (False → p2)) → False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69007082981500753703677489587 : ((p5 → (((True ∧ (p5 ∨ p3)) → (p1 ∧ (((False ∧ False) ∨ (((False ∨ (False ∨ (p1 ∨ p2))) ∧ True) ∨ (p2 ∧ p5))) ∨ p1))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186885071618848844019893098866 : (((p1 ∧ ((True ∨ p2) → p1)) → (((p5 ∨ False) ∨ p5) ∨ p1)) → ((p2 ∧ ((p2 ∧ p2) → ((p5 ∧ p2) ∨ p5))) ∨ (True ∧ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40430688076273326083910871480 : ((((((p4 ∨ ((False ∧ p2) ∧ p4)) → ((p3 ∧ (True ∨ p3)) ∧ p4)) → (p2 ∨ ((p2 → (p5 ∨ (p1 → p2))) → False))) ∨ True) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199733170376598385392657089421 : (((p1 ∨ ((p1 → True) ∧ (False ∧ p1))) → False) → (True ∧ ((p4 ∨ ((((p3 ∧ p3) → p2) → p3) ∨ p4)) ∨ (True ∨ (p2 ∨ (p4 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251112356934277269559621506027 : ((p2 → False) ∨ (((((False → p3) → p3) ∨ ((p3 ∧ (((p2 ∨ True) → p4) ∧ (p3 → p2))) → (p1 ∨ p5))) ∧ (p3 ∨ (p2 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44463860109698767364905623177 : ((((p4 → (((p3 ∨ p2) ∧ p5) → ((p4 ∨ p5) ∨ (True ∨ p2)))) ∨ (((False ∧ True) → ((p1 → False) ∧ (p5 → p1))) ∧ True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165699025298007292608633559037 : (((p3 → (((p1 ∨ p2) ∧ p4) ∨ False)) → ((p3 ∨ (True ∨ (p1 → p5))) → (p5 → p1))) ∨ (((p2 ∨ (p3 → (p1 ∨ p4))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161672463984255295270271870000 : ((p1 ∨ (p1 → ((True ∧ p4) → ((False → ((p2 ∧ p4) → (p5 ∧ p1))) ∧ (True → (p3 ∧ True)))))) → ((p5 ∨ (False → (p4 ∨ False))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171926205931929566444190618030 : (((((p2 ∨ p5) ∧ (((p4 ∨ p1) ∨ (p2 ∧ p3)) ∧ p3)) ∧ p4) ∧ (p4 ∧ p4)) ∨ ((p2 ∧ (False ∧ ((p2 ∨ p1) ∨ (p3 ∨ p2)))) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51395947672399210705122306421 : ((((p4 → (((((p5 ∧ False) ∨ True) ∧ True) ∨ (((p2 → p1) ∨ True) ∨ p4)) → p5)) ∨ False) → (False ∧ ((p5 ∧ p2) → (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61638576782859351098590044369 : ((p1 ∧ (True ∧ ((((p4 ∧ p1) ∨ (True ∨ p2)) ∨ (p5 → ((((p5 ∨ p1) → (p2 → p5)) ∨ p3) → (True ∧ (p3 ∨ False))))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620448008119401585465787318699 : (((((True → p1) ∨ ((((p3 ∨ p3) → (((((p2 ∨ False) ∧ p5) → p2) ∨ p4) ∨ p3)) ∧ (p5 ∧ p5)) ∨ (p2 ∨ (p3 ∨ p5)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_710156472348623426957124153335 : ((((((p3 → (p4 → p5)) ∨ p4) ∨ p3) ∧ (((p3 ∨ p5) → (((False ∨ p2) → False) ∧ ((p3 → p1) → ((False → p4) ∨ p2)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323678014597296843084256351798 : (p5 ∨ (((True ∧ True) → ((((((p2 ∧ p5) ∧ p2) → p2) ∨ (True ∧ p1)) → p5) ∨ ((p3 → True) ∨ p1))) ∨ (((p2 → p2) ∨ True) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33953920620089639145974452385 : ((p5 ∨ (True ∧ ((p4 ∧ ((((((p5 ∨ p1) → (p1 ∧ p3)) ∨ p3) → p4) ∨ (p1 ∨ ((p1 ∧ p5) ∧ p4))) ∧ p2)) ∨ (True ∨ p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147330165440915403734861857548 : ((((p4 → ((p1 → (p5 ∨ ((p4 ∧ p3) ∨ (p5 ∧ False)))) ∨ ((p1 → True) ∧ p4))) ∧ (p3 ∨ True)) ∨ p5) ∨ ((p3 ∧ p3) ∨ (True ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168206631665650842572107343264 : ((((p2 → p2) → False) ∨ (((p2 ∧ (((p4 → p4) ∧ (True → p1)) ∧ p3)) ∨ p2) ∨ True)) → ((True → (True → False)) ∨ ((p3 ∧ True) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
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
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343653338530768278732597361466 : (p2 → (True ∧ ((p4 → p3) ∨ (((p5 ∧ (p2 ∨ p5)) ∨ ((((p3 ∨ ((p4 ∨ False) ∧ p3)) → p4) ∨ False) ∧ False)) ∨ ((p1 → True) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164783752957907965581005921207 : ((((((True ∧ (p4 → p2)) → p5) → False) → ((p3 ∨ (p4 ∨ False)) ∧ (p3 ∧ p2))) ∨ p5) ∨ (True ∨ (p4 → ((p3 ∧ p2) ∨ (p1 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178348873529955614402780670874 : (((p3 ∧ (((False ∨ p1) → ((True ∨ p4) → p3)) ∨ False)) ∨ (p3 ∧ False)) ∨ ((True ∨ (p5 → (p4 ∧ False))) ∨ ((False → (p5 ∨ p3)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802628570626660866551438158876 : (((p2 → (True → ((p5 ∧ (((False ∧ False) → p1) ∧ ((p3 → (True → p2)) → ((p3 ∨ True) ∨ p4)))) → ((p3 ∨ p1) ∨ (p3 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186799975106535670154844207274 : ((((p4 ∨ p2) ∨ (True ∨ True)) ∧ ((p1 → p4) ∨ (p1 ∧ p1))) → (False ∨ (((p4 → p4) → ((((p5 ∧ p5) → True) → False) → p1)) ∨ p5))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : ((p5 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h9
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : ((p5 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h23 := h20 h21
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : ((p5 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h35
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h36 := h33 h34
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- One of the premise coincides with the conclusion.
        exact h39
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h43 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h44
        -- Implications on the right can always be decomposed.
        intro h45
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h46 : ((p5 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h48 := h45 h46
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h52
        -- Implications on the right can always be decomposed.
        intro h53
        -- One of the premise coincides with the conclusion.
        exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200596597425015997701161620822 : ((True ∧ (p3 ∧ (True → (p3 ∧ (True ∨ p3))))) → (p3 → ((((True → ((False → True) ∧ ((p2 ∨ p2) ∨ p4))) → p5) ∨ p2) ∨ (p4 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329167136545222509488284737533 : (True → (((p3 → True) ∨ (p2 ∨ p3)) → (((p2 ∨ False) ∧ p3) → ((((True ∧ p1) ∨ p1) ∨ (p1 ∧ (p2 → (p5 → (p3 ∧ p2))))) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
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
theorem thm_5_vars_41652691857058781791333424876 : (((((p3 ∨ p5) ∧ ((p3 ∨ p2) ∨ p1)) ∧ (p2 ∧ ((p5 → False) ∨ ((p4 → ((p3 → (p4 ∨ p4)) ∧ (p3 ∨ True))) ∨ p1)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654054563980299887313334106541 : (((((True → (((p3 ∨ p2) → ((True → (p4 → p2)) → (p4 ∨ False))) ∨ (False → (((p5 → p3) ∨ p1) ∧ True)))) ∧ True) ∨ (p3 ∧ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634059174825116225482473036931 : ((((((((p2 → (p3 → p4)) → (False ∨ True)) ∧ ((True → p1) → False)) ∨ (True ∨ ((p2 ∧ p1) → (True → False)))) → (p4 → p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40273689587909371637220906932 : ((((True → ((True ∧ (p1 → p4)) ∧ ((p5 ∨ (p3 ∧ (p1 ∧ p1))) ∨ (p2 → ((False ∧ p3) ∨ ((p4 ∧ False) → p3)))))) ∧ True) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119388385438288284300208567226 : ((p4 → (((((((p4 ∧ p5) → p1) → p5) ∧ ((True ∧ p5) ∨ (p5 → (p4 → p5)))) ∨ (p5 ∨ (p2 → p5))) ∨ p5) ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113525798304945544763058441382 : (((((p4 → (p4 → (False ∨ p1))) → (p5 ∧ p4)) ∨ (((True → (p3 → (p1 ∧ p2))) → False) ∨ (False ∧ p5))) ∨ (True ∧ p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65098729053098074875246134030 : ((p2 ∨ (p2 ∨ (p3 ∧ (p5 ∧ ((((((p1 ∨ p4) → p5) ∧ p3) → False) → (True ∧ p5)) → ((True → p2) ∧ (True → (p5 ∨ p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229359444915589414877100869251 : ((p1 → (p2 ∧ p2)) ∨ (((((p5 → True) ∨ p4) ∧ (p3 ∧ (p4 ∨ p3))) ∧ (((p4 → True) ∧ True) → p1)) → (((p5 ∧ p2) → p1) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247301179412320246716636927493 : ((False ∨ False) ∨ (((((p4 ∧ (((True ∨ p2) → (p3 ∨ p3)) ∨ (p4 ∧ False))) ∧ (p5 ∧ (p4 ∧ False))) ∧ p3) ∧ True) ∨ (p4 ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_641743918798648627196184624612 : (((((p3 ∨ p2) → ((((False ∨ p5) ∧ (((((p1 → p2) ∨ (p4 ∨ True)) ∧ (p5 → p3)) ∧ p2) ∧ p5)) → (p3 → p4)) ∨ p1)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64658617481037171102009535764 : ((p1 ∨ (False ∨ ((((((True ∨ p1) ∧ True) ∧ p5) ∨ (p4 ∨ (p5 ∨ (p2 ∨ (p4 → (((p2 ∧ p2) → p1) ∧ False)))))) → p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321315293095622144289541768276 : (p4 ∨ (p5 ∨ ((p5 ∨ ((True ∧ (p4 ∨ (p4 ∧ (True → (True ∧ p1))))) → False)) ∨ (p5 ∨ (p2 ∨ ((True ∨ True) ∧ (p5 → (p5 ∨ p1)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768727684597784570089839913757 : (((p5 ∧ ((p2 → ((p5 ∧ ((p5 ∨ True) ∧ p4)) → (p2 ∧ p5))) → (((p3 ∧ (((p3 ∨ p4) → p1) ∨ (p1 → p1))) → False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46888442963812390982824842160 : (((((((p5 ∧ True) ∧ p3) ∧ ((((p4 ∨ p2) ∨ p2) → False) ∨ (True → ((p5 ∨ (False ∧ True)) ∨ p2)))) ∨ True) ∨ p4) ∨ (p3 → True)) ∨ p2) := by
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
theorem thm_5_vars_766684664590960042848671595943 : (((p4 ∧ (False ∨ (((True ∧ (p4 ∧ p3)) ∧ (p2 ∧ ((p2 → (p2 ∧ False)) ∧ p3))) ∧ (p5 → (p5 ∨ (p5 ∨ (p4 → (False ∧ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614861759473499354247316714297 : (((((p2 → ((((p3 ∧ p1) ∧ (True ∨ p3)) → (False ∧ (((False ∧ True) ∨ p4) ∨ p1))) ∨ True)) ∨ (p2 → ((True → p2) → p3))) ∨ p1) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



