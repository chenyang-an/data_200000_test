variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340243779552839375220845203932 : (p1 → (p5 → ((p3 ∧ p5) ∨ ((True → (((p2 → True) ∧ (((False ∧ p1) ∧ p2) → False)) → ((p1 ∨ (p3 ∨ True)) → (p5 ∧ p4)))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4676004545263056966959731917 : (p5 → (p2 ∨ (((False ∨ ((p4 → ((p3 → ((p1 → p3) ∧ (((p4 → p1) → p1) → p4))) ∧ p1)) ∨ p2)) ∨ p2) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149593834176733269109262636066 : ((p3 ∧ (((p1 ∧ p5) → (p4 ∨ (False ∨ ((p3 ∧ (False ∧ (p5 ∧ (True ∧ p2)))) ∧ True)))) ∨ (p4 ∨ p4))) ∨ ((p5 ∧ p2) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337884441995382716361147620141 : (p1 → ((((((p4 ∧ ((p3 ∧ True) → True)) ∧ False) ∨ (False ∨ p2)) ∨ p2) → p2) → (p4 ∨ (((p3 → p2) ∧ ((p1 ∨ False) ∨ p2)) ∨ True)))) := by
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
theorem thm_5_vars_133734225948943380880991447434 : ((((((((p3 ∨ p1) → True) ∨ p3) ∨ (p1 ∧ p4)) → False) ∨ (p4 → (p5 ∧ ((p1 ∨ True) ∧ (p5 ∨ True))))) ∧ p3) ∨ ((False ∧ p5) → p4)) := by
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
theorem thm_5_vars_218439945591673137563950676690 : (((p3 ∧ p2) → (p1 ∧ p4)) → (((((p4 → p4) → p3) ∨ (False → (p3 ∧ (((p3 ∧ p4) ∨ p4) → (p1 ∧ True))))) ∨ (False ∨ p5)) ∨ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254757387031542492878432620522 : ((p3 ∧ p4) → ((((p4 ∨ p5) ∨ (False → False)) → ((((True ∧ p2) ∧ p5) ∧ (True ∨ (p2 ∧ p2))) ∨ (True → (p2 → (p1 → p3))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46989791618182124099690458443 : (((((True → (p5 ∨ ((p4 ∧ p3) ∧ (((p4 ∨ p2) → p5) ∧ p2)))) ∨ (((True ∧ p3) ∨ (p4 → False)) ∨ p2)) → p2) ∨ (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69021863361695232767513225206 : ((p5 → (((((((((p1 ∨ (p5 ∧ p1)) ∧ p5) → ((p1 → False) ∧ False)) → (p2 → False)) ∨ (p4 ∧ p4)) ∧ p3) ∨ p3) ∧ p3) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308587922843199618244958172442 : (p2 ∨ (((False → (True → p4)) ∧ (((((p4 ∧ p5) → (p2 → p5)) ∧ (p4 ∧ p1)) ∧ p3) ∨ (((p3 → (p4 ∨ p2)) ∧ p4) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27902434280328830229642737256 : (((False → p2) → ((((p1 ∨ (p1 ∨ True)) ∨ p3) → p3) ∨ (((False ∧ False) ∨ ((p4 ∧ (((p1 ∨ p2) ∧ p2) → False)) ∨ False)) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76303968696438743338168711606 : ((((((p4 → (False ∨ (p4 ∧ p4))) ∧ p3) ∨ (p3 ∧ (p5 → ((True ∧ ((p1 ∨ (p2 → p4)) ∨ p1)) ∧ True)))) ∨ (p2 → p2)) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → (False ∨ (p4 ∧ p4))) ∧ p3) ∨ (p3 ∧ (p5 → ((True ∧ ((p1 ∨ (p2 → p4)) ∨ p1)) ∧ True)))) ∨ (p2 → p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317742577862206068193892681810 : (p4 ∨ (((True → (((p1 ∨ ((p5 → (p3 ∧ ((True ∧ p1) ∨ (p4 ∨ p4)))) → p5)) → p5) → (True ∨ p1))) → (p4 ∨ (p4 → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44320084725721951425734447300 : (((((p2 → (p4 → p1)) ∨ ((p4 ∧ (p1 ∧ ((p5 → p3) ∧ False))) → (p2 → p4))) ∨ (p2 ∧ ((p3 ∧ p1) → (True ∨ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58845664607326160029227603793 : (((True ∧ p2) ∨ ((p5 ∨ ((p3 ∧ ((p3 ∨ (p2 ∨ ((True ∨ (p3 → p4)) ∨ (False ∨ (True → True))))) ∨ p2)) ∧ True)) → (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678613234819658646903357773853 : (((((True ∨ p3) ∧ (((p3 ∧ ((p5 ∨ True) ∨ (p2 → (p1 ∧ (p1 ∨ p1))))) ∨ False) ∧ (True ∧ True))) ∨ ((True ∧ (p5 → True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43400116989194224114919335622 : (((((False ∧ (((p2 ∧ ((p4 ∧ (p5 → (p3 ∨ p4))) ∧ p1)) ∨ p5) → p2)) → ((p2 ∨ (p5 ∧ False)) ∨ (p3 ∧ p1))) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53808175480154655351294010844 : ((((True → (((p3 ∨ (p1 ∨ p2)) ∧ p2) ∨ True)) → False) ∨ ((p4 ∨ p5) ∧ ((p1 ∧ False) → (p2 ∧ ((True → p5) ∧ (p2 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174660316052655707904459523137 : ((((p4 → p2) → False) ∧ (((p4 ∨ p5) ∨ True) ∧ ((p2 ∨ (p2 ∧ p4)) ∨ p3))) → ((p4 ∨ (p2 → (False ∨ True))) ∨ ((p1 → p3) ∧ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : (p4 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h17
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : (p4 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h29
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h30 := h2 h28
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h35
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64438297501339936297106925238 : ((p1 ∨ (((((False ∧ (False → ((((True → p1) → p2) ∧ True) ∨ p3))) ∨ p1) ∨ ((p3 ∧ p3) ∨ p1)) ∧ (p1 → False)) ∨ (True ∧ True))) ∨ p2) := by
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
theorem thm_5_vars_779392227723773432910752098656 : (((p2 ∨ ((((True ∧ (((((p1 ∧ False) → p3) ∧ ((p4 ∨ p5) → (True → p4))) → p3) ∨ p5)) ∨ (p3 → (p1 → True))) ∨ p5) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114160709484266676772655502434 : (((((((False ∧ p5) → False) → ((p1 → (True ∧ (p5 ∨ False))) ∧ (p2 ∨ False))) ∨ (True ∨ p4)) → False) → ((p2 ∨ False) ∧ p4)) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∧ p5) → False) → ((p1 → (True ∧ (p5 ∨ False))) ∧ (p2 ∨ False))) ∨ (True ∨ p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((False ∧ p5) → False) → ((p1 → (True ∧ (p5 ∨ False))) ∧ (p2 ∨ False))) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797774520304738670733111712374 : (((p1 → ((((p4 → p2) → (((p3 → p4) ∧ ((p4 ∧ p4) ∧ (p2 ∧ p1))) ∨ (False → ((p2 ∧ False) ∨ True)))) ∨ p1) ∧ (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50340162490727162916962011240 : ((((True → (((p4 ∨ p5) ∨ p2) ∧ p4)) ∧ (True → ((p1 ∨ (p1 ∨ (p1 → (p2 → p2)))) ∨ p3))) ∨ (p3 → ((True ∨ False) ∧ p3))) ∨ p5) := by
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
theorem thm_5_vars_205427981995245563118797352638 : (((p4 ∧ (p2 → p5)) → (p2 → p3)) ∨ (p3 → ((((p5 → (p2 ∨ p4)) ∧ (True ∧ ((False ∨ p5) ∧ (p3 → (p4 ∨ p4))))) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353496967264449574411021325504 : (p4 → (p2 ∨ ((False ∧ (True ∧ ((p1 → p1) → (True ∧ False)))) ∨ (p5 ∨ (((p2 ∧ (p2 ∨ (p2 ∨ p1))) → (p3 ∨ (p4 → p3))) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315074586135043025969082929729 : (p3 ∨ ((((False ∨ p2) ∨ (p4 ∨ True)) ∨ p3) ∧ ((True ∧ p1) ∨ ((p2 ∨ ((p5 ∧ False) → (((p3 → (p5 ∨ p5)) → p4) ∧ p1))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207168384796262936326309505473 : (((p4 → (p5 ∨ (False ∧ p5))) ∧ True) → (((p5 ∨ p4) ∧ (p3 ∨ p1)) → (p2 → (p5 ∨ (((p3 ∨ (False ∧ (p5 ∨ p4))) ∨ p1) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h20
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347758805254279207191212461405 : (p3 → (((True ∧ False) ∨ False) ∨ ((p3 → True) → ((((((p3 ∧ p4) → (p4 ∧ p2)) → (((p2 ∨ True) → False) → p5)) → False) ∨ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616412184061664748445643382497 : ((((((False → (((((True ∨ False) ∨ p1) → p4) → False) → False)) ∨ p5) → ((((p3 ∨ p4) ∨ (p1 ∧ True)) ∧ (p2 → p3)) ∨ True)) ∨ p5) ∨ False) ∧ True) := by
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
theorem thm_5_vars_610136717870594474027488422948 : ((((((True → (((((p4 ∧ (p5 → (p1 → (p5 → True)))) ∧ p2) ∨ p3) ∨ (p4 → True)) → (p5 → (True ∧ False)))) ∧ p1) → False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40885535679002749911022764365 : ((((((True ∨ ((False → (p1 → p2)) → (p3 ∨ True))) ∧ False) ∨ (p2 ∨ (((p3 ∧ p5) ∨ (p3 ∨ p3)) ∨ p4))) ∧ (p2 ∧ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116121753594325854156514491010 : ((((p5 → p4) → p4) ∧ (False ∨ (((p2 → p2) ∧ p1) → (p3 ∨ ((((True → p1) ∧ p1) → p5) → ((p1 ∧ p2) → p3)))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158607595103983065167026832233 : ((False ∧ ((((False → ((p5 ∧ True) ∨ p4)) → (True ∧ False)) ∨ True) ∨ (False → (p2 → (False ∨ p5))))) ∨ ((((p4 ∨ False) → False) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172936177662336078631287859298 : ((p3 ∧ ((True → (False ∨ (((False ∨ True) → (p4 ∨ p4)) → p3))) → (p5 ∨ p5))) ∨ ((p4 ∨ (p2 ∧ (False ∧ p4))) ∨ ((False → p1) ∨ p1))) := by
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
theorem thm_5_vars_330478922278959522458667366864 : (True → (p4 ∨ ((((((((p4 ∧ True) ∧ p1) ∨ p4) ∨ p3) ∧ p2) ∨ (True ∧ (p1 → True))) ∨ (((p3 ∧ (p3 ∨ p1)) → p4) ∧ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_171488717187507831770510108120 : (((p1 → ((True → ((p3 ∧ (False ∧ True)) ∨ p2)) → ((p2 ∨ p4) ∧ p4))) ∧ p3) ∨ (((p1 ∧ p5) → (p3 → ((p2 → p3) → p3))) ∨ p2)) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156651264813754263246928325600 : (((((((p5 ∧ True) ∧ p2) ∧ ((p1 → (p2 ∨ (p5 → p2))) → p3)) → (p1 ∧ p2)) → p2) ∧ p1) ∨ (p3 → ((p4 → (False → p4)) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52776362015908343573541166594 : (((((True ∧ p4) ∨ ((((p3 ∧ True) → p2) ∧ p2) → p3)) ∧ (True ∧ p2)) → (((False → p4) ∨ p5) → ((p2 → p3) → (p3 ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h21.left
      let h26 := h21.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h27 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h28 := h3 h27
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h21.left
      let h31 := h21.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h32 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h33 := h3 h32
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94341179768318248293366577624 : ((p2 ∧ ((p2 → ((((p5 → p5) ∧ p3) → p5) ∧ False)) ∧ (p5 → ((((p5 ∨ False) → p4) ∨ p1) → (p3 → ((p1 ∨ p1) → True)))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118613610002159442820271686045 : ((p4 ∨ (((False ∨ (False ∧ True)) ∧ ((False ∨ (p3 ∧ True)) ∨ ((p5 → p1) ∨ p2))) ∨ (((p4 ∧ p5) ∨ (p4 → p3)) → True))) ∨ (p1 → p1)) := by
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
theorem thm_5_vars_10321229947995505482872298832 : (((p5 ∨ ((((p1 ∧ (((False ∨ (False ∧ ((p4 → True) ∧ True))) → (p4 ∧ (p4 ∨ (p4 → True)))) → False)) ∧ True) ∧ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149491107605379931959983447565 : ((p1 ∧ (((((p5 ∧ False) ∧ (p5 ∨ True)) ∧ (True ∧ (p5 ∧ (p3 → p2)))) ∨ (p1 ∧ (p5 ∧ False))) ∨ p3)) ∨ ((p4 ∨ (True ∨ p5)) ∨ False)) := by
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
theorem thm_5_vars_789909126754163816825102182806 : (((p5 ∨ ((p3 ∧ (p2 → p1)) → (((True → ((False → p2) → ((True → (((p5 ∨ p5) ∧ p3) ∧ (p1 → p5))) ∨ p3))) ∧ p2) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148048849180763976357168131809 : (((p4 ∧ ((p2 ∨ (True ∧ ((p3 ∨ (p1 ∧ p3)) ∧ p3))) ∧ ((False ∧ p4) ∧ (p3 ∧ False)))) ∨ (p2 ∨ p3)) ∨ ((p5 → (p4 ∨ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739064804847355776495299995975 : ((((p3 ∧ p4) ∨ (((True → (((True → (p5 ∨ p1)) ∧ ((p4 ∧ p2) → True)) → (p2 → (p4 ∨ p4)))) ∨ True) ∨ (True → (p4 ∧ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349274659645323017984555153483 : (p3 → (p2 → ((((p5 ∨ ((p2 ∧ p3) → p5)) ∧ (p2 ∧ ((p2 → (p3 ∨ (True → True))) → p2))) → (((False ∧ p3) ∧ p4) ∨ p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225160347669932654944422500157 : (((p3 ∧ p4) ∧ p4) ∨ ((((False → p3) ∨ ((p1 ∧ (p1 ∧ (p2 ∧ p1))) → False)) → ((False → p5) ∧ ((False ∨ (p2 ∨ False)) ∨ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_475936308328250007732158758177 : (((((True → (((p5 ∧ p4) → p2) → (p2 ∧ False))) ∨ True) ∨ ((p2 ∧ p5) ∧ ((((p2 ∧ (False → True)) ∧ False) → (p4 ∧ True)) ∧ False))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_115333422255455115096397330403 : (((p4 ∧ ((p3 ∨ ((p1 ∧ (p5 → False)) ∨ p4)) ∨ p2)) → (p5 ∨ (((p3 → ((p5 → p5) ∨ p4)) ∨ (p4 ∨ p3)) ∧ p3))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229742423501753009281584788700 : ((p4 → (False ∨ p3)) ∨ ((p5 → ((p2 ∨ (((False → (p1 → p1)) ∧ (p3 ∨ p2)) ∨ p5)) ∨ ((p3 ∨ p3) → ((False → False) → p3)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180996421202009672016150458586 : (((p4 ∧ p2) ∨ (p4 ∨ (((False → ((p1 ∨ p3) ∧ p4)) → p3) ∨ True))) → ((p4 ∨ (True ∧ (p2 ∨ (p1 ∧ p1)))) ∨ ((False ∨ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59586638582718422970311605467 : (((p4 → p1) ∨ (((((p5 ∧ ((False → False) → p5)) ∧ (((p1 → True) ∨ (True → p3)) ∨ p3)) → p4) ∨ (p5 ∧ (p2 ∨ True))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231897242900317145331754045136 : (((True ∨ p5) → p4) → ((True ∨ (p5 ∨ p1)) → ((p2 → (((((((p1 ∧ p4) ∧ p2) ∨ p5) ∧ p5) ∨ True) ∨ False) ∧ (True ∨ p2))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2662660726409830816771393108 : (((p4 ∧ p3) ∨ (False ∨ (p1 ∧ p5))) ∨ ((p5 → True) ∨ (((((p1 ∧ (False ∨ (p5 ∧ (p3 ∧ p5)))) ∨ p1) → False) ∨ p5) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158916172304792057747038520699 : ((p1 ∨ ((p2 ∨ p4) → (((False ∧ True) ∧ ((p3 → False) ∨ ((p3 → p4) ∧ p3))) ∨ (p4 → p4)))) ∨ ((p2 → p4) → ((p2 ∨ p2) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313580741288763777222398411285 : (p3 ∨ ((((False ∨ p4) ∧ (False ∨ (p2 ∨ (((True → p4) ∧ p1) → True)))) ∧ ((p5 ∨ True) → ((False ∧ (p2 → False)) ∧ (False → p5)))) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- We need to get the left conjuct of h13 based on <expert-advice>.
        let h14 := h13.left
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h16 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h17 := h3 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47412511899128347931364628913 : (((False ∧ (((p3 → p5) ∨ False) ∧ ((p1 ∨ ((p4 ∧ p4) ∧ (((p5 ∨ (p2 → (p1 ∨ p2))) ∨ p5) ∨ p2))) ∧ p2))) ∨ (False → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264077140689337826208156146581 : (True ∧ (((True → True) → (((p5 → p1) ∨ (p5 ∧ True)) ∧ False)) ∨ ((((False → p5) ∧ p2) ∧ True) → (((True ∧ (p2 ∧ p3)) ∨ True) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164672622277757747736930076670 : ((((((p2 ∧ (((False → True) ∨ (p1 ∨ (p2 ∨ p5))) ∨ p3)) ∨ p2) → False) ∧ p1) ∨ True) ∨ ((((p3 ∨ (p5 ∧ True)) ∧ True) ∨ p3) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115167049012929185580338065217 : ((((((p1 ∧ ((p1 → p5) ∨ True)) ∨ p4) ∨ p5) ∨ True) ∧ (p2 → ((p5 ∧ ((p2 → (p4 → False)) ∧ (p1 ∨ p1))) ∨ p4))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693583283455873861276855803818 : (((((p2 ∨ (((p3 → True) → (p1 ∧ (p4 → p2))) → (False ∧ p2))) ∧ True) ∨ ((p5 ∨ (p1 ∨ ((p3 ∧ p5) → p4))) ∨ (p3 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321036522353900294477074745795 : (p4 ∨ (False ∨ (p5 ∨ ((((p3 ∧ p5) ∧ p1) ∨ True) ∨ ((True ∨ ((((p3 → (p5 ∨ (p3 ∧ p3))) ∨ (p2 → p5)) ∧ p4) ∧ p4)) → False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306459146294767072715646846305 : (p1 ∨ ((p4 ∨ False) ∨ ((((p2 ∨ p5) ∧ True) ∨ ((p1 ∧ p3) ∨ (False → ((False ∨ ((p2 → p5) ∨ p3)) ∨ (p5 ∨ p1))))) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633440185051739799374456898425 : (((((((False → ((p2 ∨ (p4 ∨ True)) ∧ (p1 ∨ ((p3 ∧ (p3 ∨ False)) ∨ (False → p4))))) ∧ True) ∨ (p5 ∧ p3)) ∨ (p4 ∧ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55458285323736264329285510004 : ((((True → ((p5 ∨ p3) → True)) → p1) → (((p1 ∨ ((p2 ∨ p1) ∧ (True ∨ (True ∧ (p4 → ((p3 → p2) ∧ p4)))))) → p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178709962041141671152799413630 : (((p4 ∨ (p4 ∧ (p1 ∧ p3))) ∨ (p2 ∧ (True → (True ∧ (p1 ∧ p5))))) ∨ ((False ∧ p3) → ((p2 ∨ True) ∧ ((p5 ∧ (p2 ∧ True)) ∧ p2)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192845540567067633172572670979 : ((((p1 ∨ ((p1 ∨ p1) ∧ False)) ∨ p3) ∧ (p3 ∧ True)) → ((((((False → p4) → p3) ∨ p1) ∨ ((True ∧ p1) ∧ p2)) → (p5 ∨ p3)) ∨ p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230306556417309915153461794481 : (((p1 ∨ p2) ∧ p5) → ((p3 ∧ ((p4 ∨ ((p5 ∨ p2) ∧ p1)) → (p4 ∧ ((p5 → p2) ∨ p1)))) ∨ (((p2 → (p5 → p4)) → p5) → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148654899416016650767449665035 : ((((False ∧ False) ∨ (((True ∧ p1) → p3) ∨ True)) ∧ (p5 ∨ (p5 → (((p1 ∨ (p4 → False)) ∨ False) ∨ False)))) ∨ ((p5 → True) ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86448482746169239376481138421 : ((((True → True) ∨ (p3 → ((False ∨ p5) ∨ (False ∨ True)))) → ((((False ∨ p3) ∧ ((p1 ∧ p4) → p5)) ∨ p3) ∧ ((True ∧ p5) ∧ True))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → True) ∨ (p3 → ((False ∨ p5) ∨ (False ∨ True)))) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165152885947488433994880297410 : (((((p1 ∧ False) ∧ (p2 → (p4 → p4))) ∧ ((p4 ∨ (p2 ∧ p5)) ∧ p1)) ∧ (True → p1)) ∨ ((((True ∨ p5) ∧ p4) ∧ (p4 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_503004628918186372616253169303 : (((((p2 ∨ p2) ∨ p1) → ((p5 ∨ ((p1 ∧ p2) ∧ ((p2 → ((True → p5) → ((p5 → p2) ∨ (p3 ∧ p5)))) ∨ (p5 → False)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35389585746779268439368935169 : ((p2 → ((((((((((True → p1) ∧ (p4 ∨ p4)) ∧ False) → p4) ∧ ((p5 ∨ False) → p4)) → p1) → p4) ∧ (p1 → False)) ∨ True) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61122467091449231573760359005 : ((False ∧ (((p2 → p2) ∧ (p5 → (p3 ∧ ((True ∧ True) ∨ p4)))) ∨ (((p2 ∨ (p1 ∨ (p4 ∨ ((p3 ∧ p2) ∨ p2)))) ∨ p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180568081916477216361348822028 : ((((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) → (p3 ∧ (True → False))) → ((p1 ∨ (p4 ∨ (p4 → p3))) → ((p3 ∨ (p5 → p2)) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h21 := h1 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h25 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h26 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h28 := h1 h26
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h34 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h36 := h1 h34
      -- We need to get the right conjuct of h36 based on <expert-advice>.
      let h37 := h36.right
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h41 : ((p4 ∧ ((p4 ∨ p2) ∨ (p1 ∨ p4))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h42
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h43 := h1 h41
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h45 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h46 := h44 h45
      -- False on the left can always be used.
      apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150178904312442355384127990116 : ((p1 → (p2 ∨ (((((p2 → ((p1 ∧ p5) ∧ (True ∧ (p1 → p2)))) → p3) ∧ p5) → p2) ∨ (p1 → True)))) ∨ ((p1 ∨ (False ∨ False)) ∧ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759650339660157483186751178013 : (((p2 ∧ ((p3 ∨ (False ∨ (((False ∨ p2) ∨ (p1 → p4)) → (p4 ∧ (False ∧ False))))) ∨ ((True ∨ (((p2 ∧ False) → p2) → p5)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203460323219417333522339417814 : ((True ∨ (((True ∨ p5) ∧ p5) → p4)) ∧ (((True → False) ∧ (((p1 → True) ∧ True) ∧ p5)) → (((((False ∧ False) → p4) ∨ p4) ∧ p1) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177698246933466406224371281320 : (((((p2 ∧ p2) ∨ (((p4 ∧ False) ∧ p2) ∨ p1)) ∨ (p1 → False)) ∧ p4) ∨ (((True ∨ (True ∧ p2)) ∨ (p3 ∧ ((p5 → p1) ∧ p2))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260804404287931886347119493852 : ((p3 → p5) → ((p4 → True) → (p4 → (((p2 ∨ p4) → (((False → ((p1 ∨ p2) ∧ p3)) ∧ (p3 ∧ (p3 ∨ (p3 → p2)))) ∧ False)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129990472424475310588350299995 : (((((p5 → (p4 → (p4 → False))) ∧ ((p3 ∧ p5) ∧ (p5 → (True → p1)))) ∨ ((p4 ∨ p1) ∨ True)) ∧ (False ∨ True)) ∧ (p4 ∨ (True ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775687578675356351269870041472 : (((False ∨ (p2 ∨ (((True ∧ ((p1 → (p5 → (p5 → ((p5 → p2) → p5)))) ∧ (p5 ∨ (True → True)))) ∧ True) → (p3 ∨ (False ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621000427227994154418477640982 : (((((True → p4) → (p1 ∧ (((p1 ∨ True) → p2) ∧ ((True ∨ p5) → ((False ∧ ((p1 → (False ∧ p2)) ∧ (True ∨ p4))) ∧ p2))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_391413825533792081279167454427 : (((((p4 ∨ (((p1 ∨ False) ∧ p3) → p4)) → ((p3 ∧ p2) ∨ ((p1 → True) ∧ (p3 ∨ ((False → p4) ∨ (p5 → (p5 ∧ p3))))))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134067573954952752274475450557 : (((((p5 ∧ (p2 → ((p1 → p3) ∨ (((p2 ∧ p5) ∨ (p5 ∨ False)) ∨ (p4 → (p2 ∧ False)))))) ∨ p2) → False) ∨ p5) ∨ (p5 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37904147461978720825865022942 : (((((p5 → (((((p5 ∨ p5) → p1) → (p1 → (p1 ∨ p1))) ∧ p3) ∧ (p4 → p5))) → ((p4 ∨ p3) ∨ p3)) ∧ (p3 → p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64018264632983901199038247581 : ((False ∨ ((p1 ∧ ((False ∨ p1) → (((((p3 ∨ p3) ∨ False) → (p3 ∧ (p2 → p5))) ∨ ((p5 ∨ False) ∨ False)) ∨ p4))) ∨ (True ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312092395941194465684498713979 : (p2 ∨ (p5 ∨ (p3 ∨ (((((p2 ∨ p4) → p5) ∧ (p3 ∨ p4)) ∧ (p3 ∧ (p3 → p4))) → ((((p3 ∧ p4) ∧ True) ∨ p4) ∧ (p3 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h15.left
    let h20 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h15.left
    let h23 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627060638827824834200031432542 : (((((((p1 ∧ p1) ∧ ((((((p3 ∨ False) ∨ (p1 → (p5 ∨ p2))) ∨ True) ∧ ((p2 ∨ p2) → p3)) ∨ p4) → p5)) ∧ True) ∧ p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135210846553327814545602278831 : (((((((p4 ∧ (p3 → (p4 → (p3 ∧ p1)))) ∨ (p3 ∨ p3)) ∨ False) ∨ p1) ∨ ((p2 ∧ False) ∨ False)) → (p5 ∨ p5)) ∨ (True → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136211326866448036554871658011 : (((p4 → ((p4 ∨ (p4 → p4)) ∧ p5)) ∧ (p3 → (p5 → (((True → (p4 ∧ (p2 → (p1 ∧ p3)))) ∨ p1) ∨ False)))) ∨ ((p5 ∧ p2) → p5)) := by
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
theorem thm_5_vars_477378903119708283581093786335 : (((((p2 ∧ ((p5 ∧ ((False ∧ p5) ∧ False)) → True)) ∨ False) → ((((((p3 → p1) ∧ (p2 ∧ p4)) → p2) → (p3 ∧ False)) → p3) ∧ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((p3 → p1) ∧ (p2 ∧ p4)) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h6
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42737530966446647303813564367 : (((True → (((p4 → (p5 → (False ∧ (True → True)))) ∨ (False → ((p3 → ((p3 → p4) → p2)) ∧ False))) → (p3 ∨ (p4 ∨ False)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115687586016722350587575963533 : (((p3 ∨ (((True ∨ p3) ∧ p2) ∧ False)) ∨ ((False ∧ ((True ∧ False) ∧ p5)) ∨ ((p5 → p4) → (p3 ∧ ((p3 → p5) → False))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183860658753316182055375536668 : ((((p4 ∧ ((p4 ∧ p2) ∧ p2)) ∧ ((p5 ∨ p1) ∧ False)) ∧ p1) ∨ ((False → False) ∨ (((p1 ∨ p4) → ((p3 → (p5 ∧ False)) ∨ False)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808122162585724285635572721464 : (((p4 → (p1 ∧ (p5 ∧ ((((p2 ∨ p2) ∧ (True ∧ ((((False → True) → False) ∨ ((p1 ∨ (False ∨ p1)) ∧ p3)) ∧ p3))) ∧ True) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152419153396972830583744196616 : (((p4 → ((False ∧ p2) ∨ p4)) → ((False ∧ p5) ∧ ((p2 → ((True ∧ (False ∧ p3)) → p5)) ∨ (p3 ∧ p1)))) → (p2 ∧ (p1 ∨ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((False ∧ p2) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → ((False ∧ p2) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47167298466342157655910894033 : ((((p1 ∨ (p3 ∧ ((p1 → ((((p3 ∧ p1) ∨ p2) ∧ p4) ∨ p5)) → p1))) ∧ (p5 → ((p5 ∧ True) ∨ (p1 ∧ p4)))) ∨ (p4 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191613742183394266506403342320 : ((p3 ∧ ((True → (p1 ∨ p4)) → (False → (p2 ∧ p4)))) ∨ (((((p4 ∨ (p1 ∧ (p1 → (p3 ∨ p4)))) ∨ p1) ∨ (True ∨ p2)) ∨ p1) ∨ p1)) := by
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



