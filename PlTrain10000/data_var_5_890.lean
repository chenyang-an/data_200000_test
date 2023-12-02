variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52448855274687160541251491779 : (((p3 ∧ (((p4 ∨ p5) ∧ (((p3 ∧ p5) ∨ True) ∨ (p2 ∧ p5))) ∨ p1)) ∧ (p1 ∧ ((p3 ∧ False) ∧ ((p5 ∧ p3) ∨ (p3 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762453619013881429418674253972 : (((p3 ∧ ((((((True → (p3 ∨ True)) ∨ False) ∨ (True ∨ (p4 ∧ p2))) ∧ (p2 → (p5 ∨ p4))) → p1) ∨ (((True ∨ p3) ∧ p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167446668843533411813254112731 : (((p3 ∨ (((p2 ∧ p2) → (p2 ∧ (p2 → p3))) → (p3 ∨ (p5 → (p5 → p2))))) → p1) → (((p2 ∧ (True ∨ p3)) ∨ p3) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112056820603268706712960985774 : ((((p3 ∧ p2) ∧ ((((p1 ∨ (p2 ∨ (p4 ∧ False))) ∨ p4) → (p2 ∨ (((p5 → p4) → p2) ∧ (False → p1)))) → False)) ∨ True) ∨ (True ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337589465844945764912746434632 : (p1 → (((p2 ∧ (p1 ∨ p4)) ∧ (p5 ∧ ((((p3 ∨ p5) ∧ ((p2 → p4) ∨ (p1 ∧ p3))) → False) → p2))) → (((p4 ∨ p2) → False) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246583255022323411620228507194 : ((p5 ∧ p2) ∨ (((p3 → True) ∨ ((p3 ∧ p1) → p5)) ∧ (p1 → (((p3 ∧ False) ∨ (True ∧ (p3 → (p2 → (False ∨ p1))))) ∨ (p1 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217882913811930701464058401651 : (((p1 → (p4 → True)) → False) → (((False ∧ ((p2 → False) ∨ (p5 → (p3 → ((((p2 → (p1 ∨ True)) ∨ p3) ∨ False) ∧ p3))))) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p4 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305875286117342128152918517390 : (p1 ∨ (((False ∧ (False ∧ p3)) ∨ (p1 ∧ True)) ∨ (((((p2 ∨ (True ∨ (p5 ∧ p2))) ∨ ((False → (True ∨ True)) → True)) ∧ p1) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165926966723215738281668292976 : (((p3 ∧ p1) ∧ ((((False → p2) ∨ ((p4 ∧ True) → (False ∧ False))) ∧ p5) ∨ (False ∨ p5))) ∨ (((p5 ∧ False) → p5) ∨ (p1 ∧ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258658457528385182568155785607 : ((p5 ∨ p5) → ((p1 → ((False ∨ ((p2 → ((True ∧ ((True ∨ p1) ∧ ((p1 → p4) ∧ True))) ∨ False)) → False)) ∧ False)) ∨ (True → (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256834970482866029428691696834 : ((p1 ∨ p3) → (((((p2 ∨ p4) ∨ (((p3 → (False ∧ p3)) ∧ False) ∨ p2)) → (((p3 ∨ p4) ∨ False) ∨ False)) ∨ p1) ∧ (p2 → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Implications on the right can always be decomposed.
  intro h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214026471918870767014111010352 : ((((False ∨ p5) ∧ p5) → p4) ∨ ((((p3 → p1) ∧ (p1 → ((p2 ∨ p2) ∧ ((p5 ∨ p2) → ((p5 ∨ (p2 ∨ True)) ∨ p4))))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111298516096913330383059383439 : (((True ∧ ((True → p2) ∨ ((p3 ∨ False) ∨ (((False ∨ ((False → False) ∧ (True ∨ p2))) → (p2 ∧ False)) → (True → p4))))) ∧ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52708506973566852017945025736 : (((p5 → (True ∧ (p4 ∧ ((((p4 ∨ p4) ∧ False) → (p4 ∨ True)) → p3)))) ∨ ((((p5 → (False ∨ False)) ∨ p2) → False) ∨ (p1 ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_306568042226707031640297316380 : (p1 ∨ ((p2 ∨ p2) → (p4 ∨ ((p4 → ((((p2 ∨ p3) → False) ∨ p3) → (((((True ∨ p2) ∧ p4) ∨ p2) → p3) ∧ (p5 ∨ p4)))) ∨ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h10 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h11 : (p2 ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h12 := h10 h11
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h15 =>
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h16 : (p2 ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h17 := h15 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h20 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : (p2 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h22 := h20 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h27
    -- Implications on the right can always be decomposed.
    intro h28
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h29
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h34 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : (p2 ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h36 := h34 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- One of the premise coincides with the conclusion.
          exact h37
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h39 =>
          -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
          have h40 : (p2 ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h38
          -- We have shown the premise of h39, we can now drive its conclusion.
          let h41 := h39 h40
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- One of the premise coincides with the conclusion.
          exact h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h44 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h45 : (p2 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h46 := h44 h45
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- One of the premise coincides with the conclusion.
        exact h47
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h48 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h49 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147101980655698824513718583387 : ((((p4 → (p5 → False)) ∨ (((True ∨ ((p4 → p5) → p3)) ∧ p2) → (False ∨ (p4 → (p5 ∨ p1))))) ∧ p3) ∨ (True ∨ ((p3 ∧ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107290734836130139597328661024 : ((((False ∨ p2) ∨ p4) ∨ (((((((p3 ∨ p1) → (p5 ∨ True)) → p2) ∧ (p4 ∧ p4)) ∧ True) → ((True ∧ p3) ∨ p2)) ∨ p2)) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∨ p1) → (p5 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
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
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654253206296384412196775835049 : ((((((p3 → (p1 → ((p1 ∧ (p1 ∨ (((p5 → p2) ∧ p2) → (p5 → ((p5 ∧ p1) ∨ False))))) → p2))) → p3) ∨ p4) ∨ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208259846838088228327100723482 : (((p5 ∧ True) ∧ ((p4 → p1) ∧ p4)) → (p3 ∨ (((((((p2 ∧ p2) ∧ (((p2 → False) → p4) ∨ True)) → p5) → p5) → p2) ∧ p4) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753868665695244667905828644181 : (((False ∧ ((p2 ∨ (False ∧ (((p5 ∨ p5) ∨ False) → p3))) ∧ (((p3 ∧ False) ∨ (p5 ∨ p1)) → (((p5 ∨ (p4 ∨ p3)) ∧ p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71752434513000085059235051695 : (((p3 ∧ (p4 → ((p5 ∨ ((p4 → p2) ∨ (p3 ∧ (p5 → False)))) ∧ (((p5 ∧ (p4 → (p4 ∧ (True ∨ p4)))) ∧ p4) ∧ p3)))) ∧ p4) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655140962435986778756796909642 : (((((False → ((p1 → (p2 ∧ ((True → True) → ((p2 → (((p3 ∧ p5) ∨ p3) → False)) → True)))) ∨ (p2 → p2))) → p4) ∨ (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343024689444619038377978119548 : (p2 → ((((False ∨ p4) ∧ p3) → p5) → (p1 ∨ ((True ∨ p5) ∧ (p3 → ((True → (((p4 ∨ (False ∧ p2)) → (p5 ∨ p4)) ∧ False)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647673357386073124365299122005 : ((((p5 → (((p5 → p3) ∧ p4) → ((p1 ∨ ((p1 ∧ False) → False)) ∨ ((p3 ∨ ((p2 → False) ∨ p1)) → (p1 ∨ (p3 ∨ False)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39307065357105333858132486669 : (((p1 ∧ (p1 ∨ (((((((False → (p3 ∨ True)) ∧ p4) ∧ (p1 ∧ True)) ∨ False) ∨ (p5 → p4)) ∨ False) ∨ ((True ∨ p5) ∧ p2)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344940110321038670367486710874 : (p3 → (((((((((p2 ∧ p5) ∨ p5) → (p1 → ((True → True) → False))) → p1) ∨ (p3 ∨ p4)) → p2) ∧ ((p5 ∨ p5) ∨ p3)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797612033943015417182167863591 : (((p1 → (((((((p5 → False) → p1) ∨ (p5 ∨ False)) → (False ∧ (p4 ∨ p3))) ∧ p5) → (((p1 → False) ∧ p2) ∧ (p2 → p5))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161502678524928823988336209241 : ((p4 ∧ (((p5 ∧ (((p3 ∨ (False ∧ p2)) ∧ p1) ∨ p1)) ∨ (p3 → p3)) ∨ (p4 ∨ (p2 ∨ p5)))) → (False ∨ ((False ∨ (p4 ∨ p5)) ∨ False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114927836160338035763370434906 : ((((((p4 → (((p1 ∨ p1) → p3) → p1)) ∨ p2) ∧ False) → (p2 ∧ p3)) → (p1 ∧ (((p2 → p5) ∧ False) ∧ (p3 ∧ True)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168178610970542590429585641448 : (((p3 ∨ (p1 ∨ p4)) ∧ (((p4 → p2) ∧ (p4 ∧ p1)) ∧ (((p3 → p2) ∧ p5) ∨ p5))) → (((False ∨ True) ∨ False) ∨ ((p5 ∧ p5) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h3.left
      let h29 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h37 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164792385324551030860372687182 : ((((p4 → ((True ∧ p1) ∨ False)) ∨ ((p5 ∧ (True ∨ ((p5 ∨ p2) ∨ p3))) ∨ False)) ∨ p4) ∨ (((p2 ∧ p5) ∨ ((True → False) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_48360259600447838518561859206 : (((p4 ∨ ((False ∨ ((p5 → p4) ∧ p3)) → (((((False ∧ p2) → (p5 → False)) ∨ p5) → p2) → ((False ∧ p3) ∨ p5)))) → (p4 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301747778181913245412391908666 : (False ∨ ((p2 → p2) ∧ (((((p3 ∧ p5) ∨ p1) ∧ ((False ∧ (p3 → False)) → (False ∨ (p4 ∧ (p2 ∧ True))))) ∧ p2) ∨ (p1 → (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38975903809609891551061892005 : ((((p2 ∧ p1) ∧ ((((p4 ∨ ((True ∨ p2) ∨ p2)) → (p3 → p4)) ∨ (p3 ∨ (True ∨ (p1 ∨ p4)))) ∨ ((p2 ∧ p2) → p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161749031980251123814450459252 : ((p3 ∨ (p5 → ((((((p5 ∨ (p4 ∧ False)) ∨ False) ∧ (p5 ∨ False)) → (p5 ∧ False)) ∧ p2) → True))) → (p4 → (p5 ∨ (p1 ∨ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216664211474453304745160328648 : ((((p4 ∨ p5) ∨ p5) ∧ p1) → ((p4 ∨ ((p3 ∨ p1) ∨ (p1 ∨ (False → (p2 ∨ False))))) → (p3 ∨ (((p3 ∧ p2) → p5) → (p2 → p2))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h1.left
        let h27 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Implications on the right can always be decomposed.
            intro h31
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h33
            -- Implications on the right can always be decomposed.
            intro h34
            -- One of the premise coincides with the conclusion.
            exact h34
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h36
          -- Implications on the right can always be decomposed.
          intro h37
          -- One of the premise coincides with the conclusion.
          exact h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h1.left
        let h41 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h44
            -- Implications on the right can always be decomposed.
            intro h45
            -- One of the premise coincides with the conclusion.
            exact h45
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h47
            -- Implications on the right can always be decomposed.
            intro h48
            -- One of the premise coincides with the conclusion.
            exact h48
        case inr h49 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h50
          -- Implications on the right can always be decomposed.
          intro h51
          -- One of the premise coincides with the conclusion.
          exact h51
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h1.left
        let h54 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h55 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h56 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h57
            -- Implications on the right can always be decomposed.
            intro h58
            -- One of the premise coincides with the conclusion.
            exact h58
          case inr h59 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h60
            -- Implications on the right can always be decomposed.
            intro h61
            -- One of the premise coincides with the conclusion.
            exact h61
        case inr h62 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h63
          -- Implications on the right can always be decomposed.
          intro h64
          -- One of the premise coincides with the conclusion.
          exact h64



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699013188793142025570017738257 : ((((False ∨ (p2 → ((p3 → False) ∧ ((p4 → p1) ∨ (p4 ∨ p2))))) ∨ (p1 → (p1 ∧ ((p4 ∧ ((p3 ∨ p3) ∨ (p3 ∨ False))) ∨ p1)))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147247551868947490999064637787 : (((((p2 ∧ p5) ∧ (p4 ∧ ((((p3 → p5) ∧ ((p5 ∧ p1) ∨ (p3 ∧ p4))) ∧ p5) ∨ p4))) ∧ p4) ∨ p1) ∨ (p3 → (True ∨ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199076459907286134767198781415 : (((((p5 → p4) ∧ (p3 ∨ p5)) → p1) ∧ p4) → ((p1 → (p5 ∧ True)) ∨ (((True ∨ ((False ∨ (p4 → p5)) → p1)) → False) → (p1 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ ((False ∨ (p4 → p5)) → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ ((False ∨ (p4 → p5)) → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214839266848973421201377214020 : (((p5 ∨ p4) ∨ (p3 ∧ p3)) ∨ (((p4 ∨ p5) → ((p1 → (p3 → (p4 ∧ ((p3 ∧ p2) ∧ ((p1 → p1) ∨ p1))))) ∨ p3)) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730246925185508395979643188867 : (((((p2 → False) → p1) → ((p1 ∧ p1) → ((p5 ∧ (((((False → False) ∨ p4) ∧ False) ∧ (p5 ∨ (p4 ∧ p1))) ∧ False)) ∨ (False ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230654287044210597055288915954 : (((p3 → p1) ∧ p4) → ((p2 ∨ (p5 ∨ ((((p5 ∨ (False ∧ (p4 ∧ True))) ∧ p5) ∨ p1) ∨ (((p4 ∨ False) ∨ p5) → True)))) ∨ (p1 ∨ True))) := by
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
theorem thm_5_vars_54067078887309198704155121330 : ((((p1 ∧ (False ∨ p5)) ∨ ((p3 ∨ (p1 ∧ p5)) ∨ p5)) → ((p1 ∧ p5) ∨ (p5 → (((p2 → p1) → (p4 ∨ p1)) ∨ (p3 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205551839238999267043992094884 : (((p4 ∨ p1) ∧ ((True ∧ p5) ∨ p3)) ∨ (p1 → (((((p5 → ((True → p1) → False)) ∧ p2) → (True ∧ p5)) ∨ p1) ∨ (False ∨ (True → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253814058019477129897727669714 : ((p1 ∧ p2) → ((p2 → (False → p4)) ∧ (p3 ∨ ((p4 → (((((p5 ∨ False) ∧ p5) ∧ (((p3 ∨ p2) ∨ True) ∧ False)) ∨ p3) ∧ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324282817441549032856777364446 : (p5 ∨ ((((False → ((False ∧ False) → p3)) → p5) ∧ p1) → (((False → (p4 ∧ p1)) → (((True ∨ False) ∧ p2) ∨ ((True ∨ p5) ∧ p4))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → ((False ∧ False) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127766823041486130256538589109 : ((True → (((((p3 ∨ p1) ∧ ((p3 ∨ p5) → False)) ∧ ((False ∧ (p4 ∨ p5)) → p5)) → (p2 → p2)) ∧ (p2 ∧ (p2 ∧ p4)))) → (p4 ∨ p2)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321155555020823089133994250365 : (p4 ∨ (p2 ∨ (p2 ∨ ((((p4 → p4) ∧ (p3 → p2)) ∧ p3) → (((p4 ∨ (((p1 ∧ p1) → (p4 ∨ True)) ∨ p3)) → False) ∨ (p5 → p2)))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640389105171897285777915617996 : (((((True ∧ p4) ∧ (((True → (p3 ∨ (False → (((p2 ∨ p3) → p5) → (p5 → p5))))) → ((False → p4) ∨ p1)) → (p2 ∧ p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747244139394134718385810068910 : ((((p5 ∨ p2) → ((p4 ∨ ((p4 → ((p2 → p5) ∨ ((((p5 ∧ p2) ∧ (((p3 ∨ p4) → False) → False)) → p1) ∨ False))) ∨ False)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_66138376383231695566875406684 : ((p5 ∨ (((p3 ∧ ((((p3 ∨ (p2 ∨ p2)) ∨ (((p3 → p1) ∧ p2) → (p1 → False))) ∧ p2) → (False ∧ p3))) → p1) ∨ (p4 → p4))) ∨ p2) := by
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
theorem thm_5_vars_670575947658731551045975531137 : (((((p4 ∨ p1) ∨ (((p5 ∨ (p4 → (((False ∧ p1) ∨ p3) ∧ p5))) → (p2 ∨ (True → p3))) ∨ (p3 → True))) ∨ (False ∧ (False ∧ p4))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314672330513484157003348341262 : (p3 ∨ ((((p1 → False) ∧ ((p3 ∨ (p1 ∨ ((p1 ∨ (p5 ∨ p5)) ∨ p5))) ∧ p3)) ∧ p1) → ((p4 ∧ True) ∨ (p2 ∨ (p3 ∧ (p1 ∧ p3)))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h19 := h4 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h22 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h23 := h4 h22
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h25 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h26 := h4 h25
            -- False on the left can always be used.
            apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h28 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h29 := h4 h28
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344491250054454144666983949178 : (p2 → (True → ((p3 ∨ (p4 ∨ (((p5 ∨ p1) → ((p2 ∧ False) ∨ False)) ∧ p5))) ∨ (p2 ∨ (((p4 ∨ (False → False)) ∨ p1) → (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354877859032387734949176972148 : (p5 → ((p1 ∧ ((((p4 ∨ True) → (((p2 ∨ (True ∨ (p3 → p4))) ∨ False) → ((p1 ∧ (True ∨ False)) ∧ True))) → p1) → (p3 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51317753430608450367606413643 : (((p5 ∨ (((p2 → ((p3 → p3) → (p1 ∨ p4))) → ((p1 → p5) ∨ (p3 → False))) ∨ True)) ∨ (False → ((False → p4) → (p2 ∧ True)))) ∨ p1) := by
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
theorem thm_5_vars_165311849758860315570527351433 : (((p1 ∨ ((p1 ∧ True) → ((((p5 ∨ p5) ∨ True) ∧ p3) → (p3 ∧ p1)))) → (p1 → False)) ∨ (p2 → ((p4 ∨ (True ∧ True)) → (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341981458581926090119693978533 : (p2 → (((((p2 ∧ (p1 → (p3 ∧ (p5 ∧ ((p5 ∧ p1) → True))))) ∨ (p3 ∧ (p5 ∧ False))) ∧ p2) → (p4 ∧ p5)) ∨ (p4 → (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51236249520054415868189618768 : (((((False ∧ p5) → False) ∧ ((p4 ∨ ((p2 → (p1 ∧ (True ∨ False))) ∨ p1)) → (p4 ∨ p1))) ∨ ((False → (p1 ∧ (p1 → p5))) ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765483816851367756869420992067 : (((p4 ∧ ((p4 → ((False ∨ ((((p2 ∨ p3) → False) ∨ p4) ∨ p4)) ∧ ((p5 → p4) → (p5 ∧ p3)))) → (((True → p3) ∨ False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66246128952329004738293474688 : ((p5 ∨ (((p4 ∨ (p4 ∧ p5)) ∧ (p4 → p5)) → ((p5 ∧ ((p4 ∨ True) ∧ (((False → True) ∧ False) ∨ (p2 ∧ (p5 → p4))))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187476402867030191078333250837 : ((False ∨ ((p3 → (True ∨ ((p3 ∧ (False ∨ True)) → False))) ∧ p3)) → (((((p3 → p3) → (p5 ∨ ((p1 → p5) ∨ p1))) → p1) ∨ p2) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723570167156008357731874998978 : (((((p1 ∨ p2) → p5) ∧ (p5 ∧ ((p4 → ((p3 ∧ (p3 ∧ p2)) ∧ (p1 ∨ p2))) ∧ (p3 ∧ ((p3 ∨ (p2 ∨ (p3 ∨ False))) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116816281240890831283798799172 : (((p4 ∨ p1) ∨ (((p5 ∨ ((((False → True) ∧ p5) ∨ p1) → (p5 ∧ (False ∨ ((p3 ∨ p1) → p2))))) → p3) ∧ (False → p3))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42385793110293658792389089978 : (((p4 ∧ (((True ∨ p2) → ((False ∧ p3) → (p5 ∨ (False ∧ (p1 ∨ (p1 ∨ True)))))) → ((True → (True → (False ∨ p2))) ∧ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113193249350615923919014144529 : ((((p5 ∧ (p2 ∨ ((((p1 ∧ p3) → p5) ∧ (p2 ∧ p4)) → (((p2 → p1) ∧ (p3 ∧ True)) ∨ p3)))) ∧ p4) ∧ (p2 → p2)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325100177820719479168804240829 : (p5 ∨ ((p2 → p3) → ((p5 → (True ∨ p2)) ∧ ((True → (False ∧ True)) → (p3 ∧ (p2 ∨ ((True ∨ p3) → ((False ∨ p1) ∧ (p5 ∨ p2))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159209708772005094181274503060 : ((p2 → ((((False ∧ p4) ∨ p5) ∨ p5) ∨ ((p4 ∨ ((p5 → p4) ∧ ((p3 ∧ False) ∨ p5))) → p5))) ∨ ((p2 ∧ False) ∨ (False → (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215113591107183432486691859247 : (((p2 → p3) → (p1 ∨ p2)) ∨ ((p5 → ((True ∨ ((p2 ∨ p3) ∨ p5)) → False)) ∨ ((False ∧ p2) ∨ ((True ∧ (True ∨ p2)) ∨ (p3 → p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164892070057068837582436503852 : (((p5 → ((p2 ∨ ((False ∧ p1) ∨ (((p5 → p5) → (p1 ∨ True)) ∧ True))) ∧ p2)) ∨ True) ∨ (p1 → ((((False ∧ p4) ∨ p1) → True) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336372188874120688796748928078 : (p1 → (((p5 → p1) → ((True → p3) ∧ (((p4 → ((((False ∨ ((p1 → True) ∨ p1)) ∧ p1) ∨ p5) → p1)) ∧ p2) ∧ (False ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656139052916542343942546864573 : (((((False → (p5 ∧ ((p5 → True) ∨ ((True ∧ (p1 ∨ (False ∧ True))) → True)))) ∧ (p1 → (((p2 ∨ p2) ∧ True) ∨ p2))) ∨ (p4 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336961286611808105703297810929 : (p1 → (((p4 ∧ (((False ∨ (p3 ∨ (p2 ∨ (True ∧ (False → p5))))) → ((p5 ∧ p4) ∨ False)) ∨ False)) ∨ (p5 → (True → p5))) ∧ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38133254972310214117059889839 : (((((p1 ∨ p2) ∨ ((p3 ∧ ((p4 ∨ True) ∧ p5)) → (p1 ∧ ((False ∨ p1) ∧ (p1 → (p4 ∨ p4)))))) ∧ ((p4 ∨ p2) ∧ p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148682199680437964383100534216 : ((((False ∨ (p1 ∨ p2)) ∧ (p2 ∨ (p1 ∧ p4))) ∨ (((p5 → ((True ∨ False) ∨ p5)) → (p1 ∧ False)) → True)) ∨ (((p1 → p5) ∨ p2) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314936945027663725478211313637 : (p3 ∨ ((p5 ∨ (((False ∧ (p4 → p5)) ∨ (p4 ∧ p4)) ∧ p2)) ∨ (p2 ∨ (((p5 ∨ (p4 ∨ p3)) ∨ p1) → ((True ∨ (p5 → p2)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181233458387718277721836278935 : ((p3 ∧ ((p3 ∧ (p2 ∨ (True ∨ (p4 → (p4 ∧ False))))) ∨ (p5 ∨ False))) → ((((True → (p5 ∨ True)) ∨ p4) → ((False ∧ False) ∧ p3)) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695731634319373961903986802683 : (((((p2 ∨ (p2 ∨ (p5 ∧ p2))) → ((((p2 ∨ p2) ∨ p4) ∧ True) ∧ False)) → ((p2 → p5) ∨ (((p1 → False) ∨ (p2 → p3)) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114864448484894682997975292095 : (((((p3 ∨ ((p5 ∧ False) → (p4 ∨ p4))) ∧ p3) ∨ ((False → True) → p1)) ∨ (False ∨ ((p2 ∧ (p3 ∨ (p3 ∨ p3))) → p2))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191775464833504963835861905163 : ((p1 ∨ (((False → p3) ∨ p2) → ((p2 ∧ p2) ∧ p4))) ∨ (p1 → ((((p3 ∨ (p2 ∨ (p2 ∧ p2))) → (True ∧ True)) ∨ (p4 ∨ False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56810896968374152659266717296 : ((((p4 ∨ False) → p5) ∧ ((((((p4 → (False ∨ p5)) ∧ False) ∨ p1) ∨ ((p2 ∨ p4) → p1)) ∧ p5) ∧ ((p4 ∨ p2) ∨ (True ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645764362998073764234229262900 : ((((p5 ∨ ((p3 ∧ p5) → (p3 → (True ∧ (p3 → (((p1 ∧ True) ∧ ((p4 → p1) ∨ ((p1 ∧ (p2 ∨ p5)) → p5))) → p2)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864965478648332536039040245 : ((p4 ∨ ((False ∨ p4) ∨ ((((p1 ∨ p1) → p1) → p3) ∨ ((((p2 ∨ p3) → ((p5 ∨ p3) → (p2 ∨ p3))) ∧ p3) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233515160430616299833283677271 : ((p1 ∨ (True ∨ p2)) → ((p4 → p2) → ((((p1 ∨ ((True → p3) ∧ p3)) ∨ p2) → ((p1 → ((p1 ∧ p5) → p4)) → p2)) ∨ (p2 → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162070197884618005121050650300 : ((p5 → (((p4 ∨ p2) → False) ∧ (p4 ∧ (False ∨ ((p2 → (((False → p5) → p2) ∧ p3)) → p1))))) → (p5 → ((True ∨ p5) → (p3 → p1)))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p2 → (((False → p5) → p2) ∧ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p2 → (((False → p5) → p2) ∧ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h26 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46214507760740785819394329617 : (((((p2 → ((p5 ∨ ((p1 ∨ p4) → (p3 ∨ p2))) ∧ (True ∧ p3))) → (True ∧ (p2 → (False ∧ False)))) ∧ (p1 ∧ p5)) ∧ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159056458487399846120123262944 : ((p5 ∨ ((p3 ∨ (((p2 ∨ p2) ∨ p4) ∨ ((p1 → p1) ∨ p1))) ∨ ((p4 → p5) → (False ∨ p4)))) ∨ (True ∨ (True ∨ (True ∧ (p1 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765584590193435661527001426408 : (((p4 ∧ (((p1 → (p1 → ((((p1 ∨ p4) ∨ (p4 ∧ p1)) ∨ p3) → p4))) ∧ p4) ∨ ((p5 ∨ (((p4 → True) ∨ p4) ∧ p2)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188116535879444913641746362853 : ((((((p2 ∨ (False ∧ True)) ∨ p3) ∧ p3) ∨ p4) ∨ True) ∧ (((((((p2 ∧ p4) ∨ (p3 ∧ p3)) ∧ (True ∨ False)) → p4) ∨ p4) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240460085624366032062233437051 : ((p5 ∨ True) ∧ ((p5 → p4) → ((True → p4) → ((p4 → (p2 ∧ (True ∨ (p3 → p5)))) ∨ ((p5 ∨ ((True → (False ∧ p4)) ∧ p5)) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249281567362026291086286927906 : ((p4 ∨ p4) ∨ (p4 → (((p5 ∧ (p5 → ((False → p2) → False))) ∨ (False → p4)) ∨ (((True → (p4 → False)) → (p1 → (p2 ∧ True))) → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256142901932223373103970891584 : ((True ∨ p5) → (p3 → ((((p2 ∨ (True ∧ (p2 ∧ ((((p5 → p2) → (False → True)) ∧ (False ∧ p2)) ∧ p3)))) ∨ (p4 ∨ True)) ∨ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167271773541880465778199986909 : ((((p5 → ((False ∨ (((p5 ∨ p4) → p2) ∨ (p2 ∧ p4))) ∧ (False ∨ False))) ∧ p2) → p5) → (p2 → ((p2 ∧ ((p4 ∧ p2) → True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258825436415796972174562570512 : ((True → p1) → ((((((p3 ∨ ((p5 ∧ p4) ∧ p5)) → p3) → p2) → (p3 ∧ (p2 ∧ p3))) ∧ (p3 ∧ (((p4 → p5) ∨ p1) → p2))) ∨ p1)) := by
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
theorem thm_5_vars_300055319839622900618546623933 : (False ∨ ((((p2 → (True ∧ ((p2 ∨ p3) ∧ p4))) ∧ (((p1 ∧ (True ∧ (True ∧ False))) ∨ (p2 ∨ p2)) ∨ (p5 → True))) ∧ p3) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40260461691437043560810929791 : ((((p2 ∨ (p5 → (p5 ∧ (((p2 → (p2 → p1)) → p1) ∨ (False → (((False ∧ p1) ∧ ((p3 ∨ p5) ∨ False)) ∧ p4)))))) ∧ p5) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68927719941171593619477749253 : ((p4 → (p3 ∨ ((((p2 ∧ p5) ∨ (p1 → p3)) ∨ (p4 → ((p5 → (p4 → ((p5 → True) → p5))) → (p1 ∨ p3)))) ∨ (p3 → p3)))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231314678714420942968254569848 : (((True → False) ∨ False) → ((p4 ∨ (((((((p5 ∨ (p4 ∨ p1)) → True) ∨ p5) ∨ p1) ∨ p2) ∨ p2) ∧ p5)) ∨ (p1 ∧ (False ∧ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714189169724827231318347073260 : (((((p3 → (False ∨ (False ∨ p5))) → False) → (((((p2 ∨ (p3 → p4)) → ((p5 → p5) → False)) ∨ ((p2 ∧ p4) → True)) ∨ p1) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118185942382162256839954811745 : ((False ∨ (False ∨ ((((p1 → ((((p3 → p1) → (p4 ∨ (p3 ∧ p5))) → p1) ∧ ((p1 ∧ p5) → p4))) ∧ False) → p5) → p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



