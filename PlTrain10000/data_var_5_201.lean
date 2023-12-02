variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645098307523623430633776888485 : ((((p3 ∨ ((((((p3 ∨ ((p1 ∨ (((True ∧ (p2 → True)) ∨ p3) → True)) → p3)) ∧ True) → p4) ∧ p2) ∨ p1) ∧ (p2 ∨ p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315818612708615727292979115876 : (p3 ∨ ((p3 ∨ p1) → ((p1 → (p3 ∧ (((p3 ∨ (p4 → ((p5 ∨ p2) ∧ p3))) → p1) → False))) ∨ ((p4 ∧ p1) → (False → (p5 → p2)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205389142566332340486816229000 : ((((False ∧ False) → True) → (p1 → p5)) ∨ ((p2 → ((((True ∧ p3) ∧ (p4 ∨ p2)) ∧ p3) ∨ p3)) ∨ ((p1 ∧ p5) → ((False ∨ False) → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684361142687644763837429617845 : ((((((((p5 ∨ (p3 ∨ p2)) ∨ (p2 ∧ p5)) ∨ p5) ∨ p4) ∨ ((p3 ∨ (p1 → p3)) ∧ p2)) ∨ (p3 ∧ ((p2 ∨ True) ∨ (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184367780464885142357066193698 : (((p3 ∨ (((p5 → p3) ∧ p1) → (p3 ∧ (True ∧ p3)))) → p2) ∨ ((p5 ∨ (True ∧ p4)) ∨ ((((p5 ∧ False) ∧ p4) → (True → p4)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139934176491486660316322465840 : ((((p2 ∨ ((p2 ∧ p5) → p2)) → (p3 → (((True → p5) → (p4 ∧ p5)) ∧ ((False ∧ p1) ∧ p5)))) ∧ (p1 → p4)) → ((True ∧ p3) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ ((p2 ∧ p5) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h7
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263798359221467469141094539441 : (True ∧ (((p2 ∧ ((p4 ∧ (p2 ∧ (False → True))) ∧ (p3 ∨ p1))) → (p2 ∧ (p2 ∧ False))) ∨ (p1 ∨ ((p5 → (False → True)) ∨ (p3 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41031372667345963931038245642 : ((((((True → p2) ∧ (p1 → (True ∨ (((p1 ∨ ((False ∨ p1) ∨ p3)) → p5) → p4)))) ∧ (p1 → (True → False))) → (p2 ∨ p3)) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609077641349012828424032944322 : ((((((p5 → (p3 ∧ (p5 → ((False ∧ p1) ∨ False)))) → (((False ∨ (p2 ∨ p1)) → (p4 ∧ p2)) → ((True ∨ False) → False))) ∨ True) ∨ p2) ∨ False) ∧ True) := by
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
theorem thm_5_vars_193006808204376519870631956709 : ((((p5 ∨ (p3 ∧ (p4 ∧ p5))) → p5) → (p1 ∨ p4)) → ((False ∨ p3) ∨ (((((False ∨ p5) ∧ ((p2 ∨ True) ∧ False)) ∨ p3) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690694228504719311418773060617 : (((((p5 ∨ (True ∨ ((p4 ∨ (((False → True) → p1) ∧ (p2 ∨ True))) ∨ p5))) ∨ False) → (((False ∨ (p4 → True)) ∧ (p5 ∨ p4)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207064961856116097197365248580 : (((p2 ∧ ((p4 ∧ p1) ∨ p3)) ∧ p2) → (p2 ∧ ((((p5 → False) → p1) → p3) → (((p2 → p1) ∨ p1) → (((True ∧ False) ∧ p2) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h22 := h12 h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41134093301459701441309844363 : (((((((p4 ∧ p3) ∧ p4) ∨ (p1 ∨ (((p3 → (True ∧ ((False ∨ p4) → p4))) ∨ True) ∨ p3))) → p5) ∨ ((p2 → p1) → p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727057308381418461849715936931 : (((((p4 → False) → False) ∨ ((((((((((True ∧ (True ∧ p5)) ∧ True) ∧ p3) ∧ p2) ∨ True) ∨ p4) ∨ p2) → (p3 ∨ p5)) ∨ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166513070965205502405226899868 : ((p4 ∨ (((((p3 ∧ ((True ∧ p1) → p2)) ∧ p3) → p1) → (p3 ∧ p4)) ∧ (p5 → False))) ∨ ((True → (((False ∧ False) → False) ∧ p5)) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598639799324547906254930368768 : (((((p3 ∨ (p2 ∨ p1)) → ((p1 ∧ ((p4 ∨ (p1 ∨ True)) → (True ∧ (p1 → (False → p3))))) ∨ (p4 ∧ ((True ∧ False) → p5)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179845056139687199897387138109 : (((p2 ∨ ((p2 → ((p5 → p1) ∨ ((p1 ∧ p1) → p5))) → p5)) ∧ p1) → ((False ∧ True) ∨ (((p4 → p2) ∨ (True ∨ (p2 ∨ p4))) ∧ p1))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712104334244655843864309500459 : (((((p2 ∨ ((p1 ∧ p4) ∨ False)) ∨ p1) ∨ (p4 ∨ ((True ∨ (p2 ∧ p3)) ∨ (p1 ∨ ((p2 ∧ (((False ∧ False) → True) → True)) → p2))))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157453889233684573315866971246 : (((((((p3 ∨ (p3 ∨ True)) ∧ ((False ∨ p4) ∨ p5)) → (p2 ∨ False)) → p1) ∧ p5) ∨ (True ∨ p3)) ∨ ((True ∨ ((p3 ∧ p1) → False)) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160163657386913676016735915682 : ((((p1 ∧ ((p5 ∨ False) ∨ p4)) ∧ ((True → ((p5 → p2) ∧ p2)) ∨ (p1 ∨ True))) ∧ (p1 ∨ p1)) → ((p3 ∧ True) ∨ (p2 → (p2 → p1)))) := by
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
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- Implications on the right can always be decomposed.
            intro h21
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- Implications on the right can always be decomposed.
            intro h24
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- Implications on the right can always be decomposed.
            intro h28
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Implications on the right can always be decomposed.
            intro h31
            -- One of the premise coincides with the conclusion.
            exact h29
    case inr h32 =>
      -- False on the left can always be used.
      apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- Implications on the right can always be decomposed.
        intro h37
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h39
        -- Implications on the right can always be decomposed.
        intro h40
        -- One of the premise coincides with the conclusion.
        exact h38
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h44
          -- Implications on the right can always be decomposed.
          intro h45
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- One of the premise coincides with the conclusion.
          exact h46
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h50 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h51
          -- Implications on the right can always be decomposed.
          intro h52
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h53 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h54
          -- Implications on the right can always be decomposed.
          intro h55
          -- One of the premise coincides with the conclusion.
          exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52014227378891064542933513094 : (((p4 ∧ (p2 → ((((((p1 → p1) ∧ p2) ∨ False) ∨ (False ∨ True)) ∧ p2) → p1))) ∨ (((((p4 ∧ p4) → p2) → p1) → p4) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323717193930753168242254809717 : (p5 ∨ (((p5 → ((p2 ∧ p3) ∧ (p4 → p4))) ∧ ((p4 ∨ p4) ∨ (True ∨ ((p4 → p1) → (p5 → p4))))) → (p5 → ((p5 ∧ False) ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110972967809638025507142057009 : (((((p5 → ((p4 ∧ p5) → (False → ((p5 ∧ (p1 → ((p2 → p3) ∨ False))) → (True → p4))))) ∧ p5) → (p1 ∨ p3)) ∧ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149054688509516575533757336565 : (((p4 → (p3 ∧ True)) ∨ ((p5 → (p5 ∧ (True → (True → (p2 ∨ True))))) → (((p1 ∨ p5) → p1) → p1))) ∨ ((True → False) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247792919108296504236255264519 : ((p1 ∨ p1) ∨ (((p1 ∨ ((p1 ∧ (p2 → p2)) ∨ p3)) ∨ ((p4 ∧ p4) → (True ∨ p1))) ∨ ((p4 ∧ ((p5 → p4) ∨ p5)) → (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_62558214703134138045821432382 : ((p3 ∧ (p4 ∨ (((True → (True → True)) ∧ True) → ((((p1 ∨ p1) → (p1 ∨ p1)) ∧ (p5 → p3)) ∧ (p2 ∧ (False → (p2 → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594638692085546775247626433633 : ((((((((((p2 → p5) ∧ p4) → (p4 ∧ p4)) ∨ False) ∧ ((p1 ∨ True) → p5)) ∨ p3) → ((((p4 ∨ p4) ∧ p5) ∧ p1) ∧ p3)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300566780588853023208556240942 : (False ∨ ((p3 ∧ ((p2 ∨ ((p3 → (p1 ∨ False)) ∨ (((True ∨ (p4 ∨ (False ∧ True))) → p3) ∨ p2))) → p3)) ∨ ((p4 ∧ p2) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_356263435342630166178933183724 : (p5 → (((p4 ∧ ((p4 → p4) → p5)) → (((True ∨ (p1 ∨ True)) → (p3 ∧ False)) ∨ p4)) ∨ ((p4 ∨ (p5 → p2)) → (p1 ∨ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47333425701060574645158569487 : ((((p2 ∧ p4) ∧ (((((p2 ∨ True) ∧ (((p5 → False) → (True ∨ False)) → p5)) ∧ p3) ∨ (p2 → True)) ∧ (False ∨ False))) ∨ (p2 → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326109821459500882561091171789 : (p5 ∨ (p1 → ((((((True → p2) → p4) ∧ ((p3 ∨ p4) ∨ True)) → (p2 → True)) → (p2 → ((p4 ∧ p3) ∧ (p5 ∨ False)))) ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137860366248538712040293096333 : ((p3 ∨ (p4 ∧ ((((False ∨ ((False ∨ p2) ∧ False)) ∧ (False → ((p3 ∨ p5) → (p2 ∧ p3)))) → (p3 ∧ p4)) → False))) ∨ ((False ∧ p3) → p1)) := by
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
theorem thm_5_vars_208149931917906562730896394140 : ((((True → False) → p5) → (True ∧ True)) → ((p3 ∨ (p1 → p4)) ∨ ((p2 ∨ (p4 ∨ (((False ∨ p2) ∧ True) → ((p4 → p2) ∨ p1)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175272763132080805345174151670 : ((p2 ∨ (p3 ∨ ((p4 ∧ False) ∧ (((p5 ∨ p2) → p3) ∨ ((p4 ∨ p4) → p4))))) → ((False → p3) ∧ (p5 → (((p4 ∨ p4) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133635346425106570193230639502 : ((((p3 ∨ (p1 ∨ ((((p3 → (p5 → (p1 → p2))) → ((p1 ∨ (False ∧ p5)) ∨ p2)) → p5) ∨ p1))) → False) ∧ p1) ∨ ((p4 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244366979861785044442614576616 : ((False ∧ p1) ∨ ((((p5 ∨ (p4 → p2)) → p3) → (p2 → (((p5 ∨ (((p1 ∧ (p2 ∧ False)) ∧ p1) → p1)) ∧ p2) ∨ (p2 ∧ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159355265996067530059046718211 : (((((True ∨ p5) ∨ ((p1 → (((p5 ∧ True) ∧ (p2 ∧ False)) ∨ (True ∧ p5))) ∨ False)) ∧ p1) ∧ True) → (((True → p5) ∧ p4) ∨ (p4 → p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351211113263865006407491816319 : (p4 → (((p1 → (p3 ∨ ((True ∧ (False ∧ (((p5 → p5) ∨ p2) ∨ p4))) ∨ (((p2 ∧ p3) ∨ p2) ∨ p1)))) ∧ p3) ∨ (p3 ∨ (p3 ∨ p4)))) := by
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
theorem thm_5_vars_56411663548284077095712958717 : ((((p2 → (p2 ∨ p4)) → p5) → (((p1 ∨ False) ∧ (((False ∧ p5) ∨ ((((p3 ∧ p2) ∨ (True ∨ p2)) ∧ p1) → p3)) → p3)) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p2 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207142108612755867791718956737 : (((False → (p2 ∧ (p4 → p2))) ∧ p4) → ((p1 ∨ (((True ∨ False) ∧ p2) → (False ∨ (((True ∨ (True ∧ p3)) ∧ p4) ∧ (p1 ∨ p5))))) ∨ True)) := by
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
theorem thm_5_vars_258775620450608340992077550422 : ((True → False) → (((((p5 ∧ ((((p2 → (p1 ∧ (True → False))) ∨ p3) ∧ False) → p4)) → False) ∧ p1) ∧ (p3 ∨ (False ∨ p2))) ∨ (False ∧ p1))) := by
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
theorem thm_5_vars_149593579735262863677747459793 : ((p3 ∧ ((((((p1 → p3) ∨ p4) ∧ p5) → p2) ∧ ((((p2 ∧ p5) ∧ False) ∧ p2) ∨ p4)) ∨ (p1 → p1))) ∨ (p5 → (True ∧ (True ∨ p1)))) := by
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
theorem thm_5_vars_180725187310246422446837974065 : (((True → ((True ∧ p2) ∧ p3)) ∧ (p2 → (p5 ∧ ((p5 → p1) ∧ p2)))) → (((p3 → p3) → p4) → ((p3 → False) → ((p3 ∧ True) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119281380248512838497751975466 : ((p3 → (((((p4 ∨ False) → (p3 ∧ ((False → p2) → ((False → p4) ∨ p2)))) → ((False ∧ p4) ∧ (p5 ∨ p2))) ∨ p5) ∨ True)) ∨ (p2 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327186674742715332533342237058 : (True → ((p2 ∨ ((p2 → p1) → (p5 → ((p2 → p3) → (False ∨ (p2 ∧ ((p5 ∨ ((p3 ∧ False) ∨ (p3 ∨ (False → p5)))) ∧ p1))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219756178442539070496329192786 : ((p2 → ((p3 → p1) ∧ p1)) → ((p3 → (p5 ∨ False)) ∨ (((p3 ∨ ((False ∧ (p2 → p3)) ∨ (p5 ∧ (p2 ∨ (p1 ∧ p1))))) ∧ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4221519222562113285078978713 : (p5 ∨ ((((False ∧ (((((p1 → (p3 → True)) ∨ (p5 ∨ p4)) ∧ p5) ∨ p1) ∧ p3)) ∨ p5) ∨ (p1 ∧ False)) ∨ (True ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660992950236989371997041217234 : (((((((p2 ∨ p2) → (p4 ∧ (((p4 ∧ ((p2 ∧ True) → False)) ∨ (p5 ∧ True)) → (True ∧ False)))) ∨ p5) ∧ (p4 ∨ p1)) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149209559512762930361884127860 : (((False ∧ True) ∨ (p3 ∨ (p2 ∨ (p1 ∨ ((True ∨ (((p5 ∨ False) ∧ True) ∧ (True ∧ (p5 → p3)))) ∧ p3))))) ∨ ((p2 → p2) ∨ (False ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54911385876663110333029919315 : (((((False → (True → p4)) ∧ p2) → True) ∧ (((p4 → (((p1 ∨ p2) ∧ p4) ∧ (p2 ∨ True))) ∨ (p5 ∨ False)) ∨ (p5 → (True ∨ True)))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190352199724877090151384451806 : (((((p1 → True) ∨ p3) → (True → (p2 ∨ p3))) ∨ True) ∨ ((((p2 ∨ False) ∨ p5) → (p2 ∧ p3)) ∨ ((p1 ∧ True) → (p3 ∨ (p1 ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617061911845975352197102405814 : ((((((p2 → p1) ∧ ((False ∨ (p2 ∨ p3)) → False)) ∧ (((p5 ∨ (p4 → p2)) → (p1 ∧ (p1 → True))) ∧ (p2 → (True → p3)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329522349726738276906462658105 : (True → ((p1 ∧ p5) ∨ ((((p1 ∧ p4) ∨ p3) ∨ (False → p1)) ∨ (((p3 → False) ∧ p3) ∧ (((p2 ∨ (p2 ∨ p5)) ∧ p2) → (p1 ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140082169253712537341347148554 : ((((p4 → True) → ((p5 ∨ (((p1 ∨ p2) ∧ (p4 ∧ p5)) ∧ p5)) → ((p4 ∧ p3) ∧ (True ∨ True)))) ∨ (p2 ∨ p1)) → ((p3 ∨ True) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311884005737447912171255989053 : (p2 ∨ (p2 ∨ (((((((p1 ∧ (p1 ∧ p4)) ∨ p4) ∨ p2) → False) → p5) ∧ (False → (p5 ∨ p4))) ∨ ((True ∧ ((p2 ∧ p4) → p4)) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57736465245546763419921472456 : ((((p4 ∨ False) → p2) → ((((p2 → (True ∧ p1)) → p4) ∨ (p3 ∨ ((p5 → p1) ∧ p5))) ∧ (((p2 → p2) → p5) ∨ (False ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326002162739599717191957308159 : (p5 ∨ (True → ((p1 → (((p2 ∨ (p3 ∨ p5)) → True) → p1)) → (((p5 → False) ∨ False) ∨ (p1 → ((False ∨ (True ∧ (True ∧ True))) ∨ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611859563221259444281543608871 : (((((p4 → (((False ∨ (p2 ∧ False)) → ((p3 ∧ (((False ∨ p1) ∧ (p1 ∨ p4)) → p4)) ∨ p2)) ∧ (p1 ∨ (p1 ∨ p5)))) → p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134896561585796876783943035948 : (((p5 → ((p3 ∧ False) ∨ (((p3 ∨ p3) → False) ∨ (p2 → ((p3 ∨ False) → ((False → (True ∧ p2)) ∧ p3)))))) → p2) ∨ (p3 ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599511752716114063330358640339 : (((((p2 ∨ False) ∨ ((((True ∨ (True ∨ False)) → p5) ∨ p3) ∨ (((p2 ∨ (True → p4)) → (p3 ∨ p4)) ∨ ((True → p1) ∧ False)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53571505242597681508447043717 : ((((False ∧ (True ∨ (False → (p5 → (p3 → p5))))) ∨ False) ∧ ((p4 ∧ ((False ∨ (p1 ∧ (p5 ∨ p4))) ∨ p3)) ∧ (p4 ∧ (True ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53465830518478585504418860151 : ((((p4 ∧ p2) → (p2 → ((False → ((p5 → False) → p2)) ∨ p1))) → ((p5 ∧ p2) ∧ (((p3 ∨ False) → p4) ∨ ((p1 ∧ p5) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224824834260622108403801180293 : ((p4 → (p1 → True)) ∧ (((((((False → p2) ∨ p3) ∨ p1) → (p4 → p1)) ∨ p2) ∧ p5) ∨ (((p1 → p5) ∨ ((p4 → p2) → True)) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50845786861800416820475955989 : ((((True → ((p5 ∨ (False ∧ True)) → ((((p2 ∨ p4) → p4) ∨ (False → p3)) → False))) ∧ False) ∧ (((p2 ∨ False) ∨ p3) → (p4 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41283385068394244899939694036 : (((((p1 ∧ ((True ∨ (((False → False) → False) ∧ p1)) → (p4 ∨ (p5 ∧ True)))) ∨ (False ∧ p1)) → ((p5 ∧ (False → True)) ∨ p2)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316930658283451746976755454301 : (p3 ∨ (p2 → ((p2 ∧ (((False ∨ p4) → p4) → (((p1 → p1) ∧ (p1 ∧ p1)) → ((True ∨ p3) → p4)))) ∨ (True ∨ ((p2 ∨ p2) → p5))))) := by
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
theorem thm_5_vars_351244382405660528688807830430 : (p4 → ((((p2 → True) ∧ p2) ∧ (p3 ∨ (((p2 ∨ (p5 ∨ ((p4 ∨ ((True ∧ p4) → p4)) ∧ p2))) → p4) ∧ p1))) ∨ ((p5 ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655295868554613221927175614150 : (((((p1 ∧ ((p4 → ((p1 ∨ False) ∧ ((p5 ∧ False) ∧ (p3 ∧ (((p3 ∨ True) → p3) → p2))))) → p4)) ∧ (p1 ∧ False)) ∨ (p4 → True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_226316108870664958417608530714 : (((p5 ∨ False) ∨ False) ∨ (p5 ∨ (((True ∧ p1) ∨ True) ∨ ((False ∨ False) ∧ (((((p5 → p2) ∨ p3) ∧ p3) ∨ False) ∨ (p3 → (p4 ∧ p1))))))) := by
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
theorem thm_5_vars_217418050960731278881637581713 : (((p1 → (False → False)) ∨ p5) → ((((True ∧ p1) ∧ (p2 ∨ False)) ∨ ((False ∧ p2) ∧ ((p1 → (p5 ∧ False)) → False))) ∨ ((p3 ∨ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601224970442367498459276353330 : ((((p2 ∧ (((p3 ∧ p3) → (p4 ∨ ((((True ∨ False) ∨ (p4 → (p4 ∧ (True → (p2 ∧ p3))))) ∧ (p1 → p4)) → p4))) → p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200854219319142765014002893270 : ((True ∨ ((p2 ∨ False) → (False ∧ (True → False)))) → (((p4 ∨ (p3 ∨ ((((p1 → (True ∨ True)) ∧ p4) ∨ (p2 ∨ p4)) ∨ p4))) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_773291412385860678919134604372 : (((False ∨ (((((p1 → p5) ∧ False) → True) → ((((p2 ∨ p5) → (p5 ∧ False)) ∨ (p5 ∧ (p2 → p2))) ∨ (True ∧ (p2 → True)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262289328530956682006119550622 : (True ∧ (((((p1 → False) → p2) → (p1 ∨ (p2 ∧ ((p5 ∧ True) ∧ ((p5 ∧ p4) ∧ p5))))) → ((p4 ∨ (p1 ∨ (p1 ∧ True))) ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656241232937653241919991482700 : (((((p5 ∨ ((False → ((((p5 → False) ∨ p3) ∨ p2) ∧ p5)) → (p5 ∨ p5))) → (((p5 ∨ p5) ∨ (p5 → False)) ∨ p2)) ∨ (False ∧ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → ((((p5 → False) ∨ p3) ∨ p2) ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113864195931406243663587488170 : (((p4 → (((p1 ∧ ((p3 → (p3 ∨ True)) ∨ (p5 → p1))) ∨ ((p3 → False) ∨ (p5 ∧ (p1 ∧ p3)))) ∨ False)) → (True ∧ p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798018718471224003725877302901 : (((p1 → ((((p5 ∨ p5) → (True ∨ False)) → (((p5 ∧ (((p1 → p3) ∨ p4) ∧ p2)) ∧ (p3 → False)) ∨ p1)) ∧ (p5 ∨ (p5 → p1)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731934171862440538087287336712 : ((((p5 → (p4 ∨ p3)) → (((p4 ∧ True) ∧ (p2 ∨ False)) ∨ (True ∧ ((p1 ∨ p2) ∨ (((((True ∨ True) ∧ p5) → True) ∨ True) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68266298410193993207345071291 : ((p3 → ((((p2 ∧ ((p4 ∨ True) ∨ p5)) ∨ ((p3 → p2) → True)) ∧ (p1 → (p5 ∧ (p2 ∨ (p5 ∧ (True ∧ p4)))))) ∨ (True ∨ p5))) ∨ p4) := by
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
theorem thm_5_vars_927575038043121550662964348944 : ((((((p4 → ((p5 ∧ (p1 ∧ True)) ∨ False)) ∨ p4) → p5) ∧ (((p5 → p5) ∧ (p4 ∧ ((True → False) ∧ (p3 → (p4 ∨ p2))))) ∨ p4)) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : ((p4 → ((p5 ∧ (p1 ∧ True)) ∨ False)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315170373200058120602980591726 : (p3 ∨ ((p4 ∧ (True ∨ (p5 ∧ (p3 ∧ p2)))) → ((p5 ∨ (p3 ∨ p2)) → (((False ∧ (p5 ∧ True)) → p2) ∧ ((p1 ∨ p2) ∨ (p4 → p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h1.left
      let h29 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687390505129595109368312885679 : (((((((p2 → ((p5 ∧ p2) ∨ (False ∧ ((False ∧ p2) ∧ p2)))) ∧ False) ∨ True) ∨ p3) ∧ (False ∧ (True ∨ (False ∧ ((p3 → p4) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655494595095673666591889645329 : (((((((True → ((p5 ∨ ((p1 ∧ True) ∨ p5)) ∨ p2)) → (True ∧ ((False ∨ (p4 ∨ p1)) ∨ p2))) ∧ True) → (p5 ∧ p2)) ∨ (True ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213366712143096598260049659547 : (((p5 ∧ (p1 ∧ p4)) ∧ p5) ∨ (p1 → (((False ∨ (False ∧ p4)) ∧ (p3 ∨ p1)) ∨ ((p4 ∨ p4) → (((p1 → (p5 → False)) → p1) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53044721725412965202621904567 : ((((p3 ∨ False) ∧ (p2 ∧ ((((p3 ∨ False) ∨ p1) ∧ p1) → False))) ∧ ((((p5 → p2) ∨ (((p4 ∧ p4) ∧ p1) ∨ p2)) ∧ p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179066677212532380200355028474 : ((True ∧ ((p5 ∨ ((p3 → (False ∧ (False ∧ p1))) → (p4 ∧ p1))) → p2)) ∨ ((p2 → (p2 → ((p1 ∧ True) ∧ p5))) ∨ ((False ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_564200571926810748744190036514 : (((p5 ∨ (True → (((((p1 ∨ p3) ∧ p2) ∧ p5) ∧ p3) ∨ ((False ∧ p2) → ((p3 ∨ (p5 → True)) → ((p3 ∨ (True ∧ True)) ∧ False)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h2.left
    let h12 := h2.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657970853636863618419746594297 : ((((p2 ∧ ((((p2 → p3) → (p1 ∨ p2)) ∨ (((True → p2) ∧ p1) ∨ ((p4 → p5) ∨ ((p3 ∧ p1) ∨ p5)))) ∨ True)) ∨ (p4 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_64386260059072115127933744509 : ((p1 ∨ (((((p1 ∨ p4) → (((p3 ∨ p5) ∨ p5) ∨ ((False → p3) ∧ (True → p2)))) ∨ (True ∧ (False ∧ (False ∨ p3)))) ∧ p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191678323030872727005898211064 : ((p5 ∧ ((True ∧ (False → p4)) → (p4 → (p2 ∧ True)))) ∨ (((p2 ∧ ((p3 ∨ False) → (p4 → p1))) ∨ (False ∨ (p4 ∨ True))) ∨ (p2 ∨ p3))) := by
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
theorem thm_5_vars_165985720328836165246911471860 : (((False ∧ p4) ∨ (((p1 → p2) ∨ p5) ∨ (False ∧ (((False ∧ False) ∨ p4) ∧ (False ∧ p2))))) ∨ ((True ∨ p4) ∨ (p4 ∨ ((False ∧ True) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188313810488990408301002127596 : (((p4 → (True → (p3 ∧ (p2 → (p1 ∧ p5))))) ∨ True) ∧ ((p3 → ((p2 → (False ∧ (p1 → ((p3 ∧ (p3 → True)) ∨ p4)))) → p1)) ∨ True)) := by
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
theorem thm_5_vars_134190355221977537488093410455 : (((((p5 ∧ p3) ∨ (p1 → (True ∨ (((p4 → p2) ∧ p5) ∧ p2)))) → (True ∧ (False ∨ ((True ∧ p4) → p5)))) ∨ p1) ∨ ((True → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138167894007830786157027938251 : ((p1 → ((((p3 → ((p1 ∧ p1) ∨ True)) ∧ p4) ∧ ((True → (p5 ∧ p5)) → p1)) → ((p3 ∨ (p2 → p3)) ∨ p1))) ∨ (p5 → (p1 ∨ p2))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761782735644466283747033052487 : (((p3 ∧ (((((p1 ∧ (((False ∨ (p2 ∧ ((p1 ∧ True) → p1))) → ((False → p1) → True)) ∨ (False ∨ False))) ∨ p2) → False) ∧ p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53049243148882777826180614967 : ((((p3 ∧ p2) ∨ (((p4 → p2) ∨ ((p1 ∨ p3) → p2)) ∨ p1)) ∧ (True ∨ (((((True → True) → False) ∨ True) ∨ p5) → (True ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263835548049420322886561007887 : (True ∧ (((p3 ∨ (p4 → p4)) ∧ ((((((p2 → p5) ∨ True) → p1) ∧ False) → p5) → p2)) → (p2 ∨ (p5 ∧ ((p3 ∧ (p2 → p2)) ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((((p2 → p5) ∨ True) → p1) ∧ False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (((((p2 → p5) ∨ True) → p1) ∧ False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115395919817628732009374718118 : (((p1 ∧ (p2 ∧ ((p5 ∧ p3) ∨ (p4 ∧ p4)))) ∧ (True ∧ (((False ∨ p1) → (p5 ∨ (p5 ∧ p2))) ∧ ((True → p2) ∧ True)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173886592144089170000798272388 : (((((p2 ∧ (p3 ∧ (p1 → p1))) → (p2 → ((p4 ∨ p2) → True))) ∨ p2) → p1) → (((p4 → p5) → ((p5 → False) ∨ p3)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159957311087995178603094739838 : (((((p4 ∧ p1) ∨ (p1 ∧ (((True ∨ p1) → ((True ∧ p5) ∨ p2)) → p5))) → (True ∨ p3)) → p4) → ((((p2 ∧ p3) ∧ p4) ∧ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ p1) ∨ (p1 ∧ (((True ∨ p1) → ((True ∧ p5) ∨ p2)) → p5))) → (True ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



