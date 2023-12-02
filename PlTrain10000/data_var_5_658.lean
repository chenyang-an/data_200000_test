variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667702291162115541517354354717 : ((((p4 ∧ ((p1 → ((True → True) → False)) → (p4 ∧ (((p2 → False) → (p1 ∧ (p5 → (False ∨ p3)))) ∧ False)))) ∧ ((p4 → p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950973235943079489515523238321 : ((((True ∨ (p2 ∨ p4)) ∧ ((True → p1) ∧ (p4 ∨ ((False ∧ (((p5 ∧ p1) ∨ p3) → True)) → (p4 ∧ ((p5 ∧ (p2 → p1)) ∧ True)))))) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h19 := h15 h18
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h22 := h15 h21
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h28 := h24 h27
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h30 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h31 := h24 h30
        -- One of the premise coincides with the conclusion.
        exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248049075645426979283095998486 : ((p1 ∨ p5) ∨ ((p4 ∨ False) ∨ (((False ∨ p2) ∧ (((p2 ∧ (p3 ∨ (True ∨ (p2 ∧ p2)))) ∨ True) ∧ (p2 → p2))) ∨ ((p4 → False) → True)))) := by
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
theorem thm_5_vars_57536959750064922171232665121 : (((p5 → (p5 → p1)) ∨ (((True ∧ (p4 ∨ (False ∧ p2))) ∧ ((False ∧ p3) → p3)) ∨ (p4 → (((p3 → (p5 ∨ p2)) ∨ True) ∨ False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299199892853300365303317764404 : (False ∨ (((((p5 ∧ p1) ∨ (((((True ∧ p3) ∧ True) ∨ ((p2 ∨ (p5 ∨ p2)) ∨ (False ∨ p1))) ∧ True) ∨ p3)) ∧ False) ∧ (p1 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47905180876510135071654576704 : (((((p5 ∧ (p1 ∧ ((p2 ∧ True) → (((p1 ∨ (True → ((p4 → p4) ∧ p3))) ∨ p4) → True)))) ∨ p2) → (p3 ∨ p4)) → (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_829139933526207411314222863413 : ((((False ∨ (((((p4 ∧ p1) → (p2 → (((p4 ∧ (p1 ∨ p4)) → ((p4 ∧ p4) ∧ False)) ∧ False))) → p1) ∧ p5) ∧ (p2 → False))) ∧ True) → p1) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∧ p1) → (p2 → (((p4 ∧ (p1 ∨ p4)) → ((p4 ∧ p4) ∧ False)) ∧ False))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h11.left
        let h18 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h11.left
        let h21 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h20
      -- Conjunctions on the left can always be decomposed.
      let h22 := h13.left
      let h23 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h11.left
        let h26 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h11.left
        let h29 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h28
      -- Conjunctions on the left can always be decomposed.
      let h30 := h13.left
      let h31 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h11.left
        let h34 := h11.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h35 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h36 := h7 h35
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h11.left
        let h39 := h11.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h40 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h41 := h7 h40
        -- False on the left can always be used.
        apply False.elim h41
      -- Conjunctions on the left can always be decomposed.
      let h42 := h11.left
      let h43 := h11.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h44 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h45 := h7 h44
      -- False on the left can always be used.
      apply False.elim h45
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h46 := h8 h10
    -- One of the premise coincides with the conclusion.
    exact h46
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53143027582899651820232857812 : ((((True → (((p2 ∧ p5) ∧ ((p1 ∧ False) ∨ p2)) ∨ False)) ∧ True) ∨ (p4 → (((p4 → (p1 → (True ∨ p4))) ∧ (p3 → p3)) ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36787457065262019882192695051 : ((p5 → ((((p3 → ((p2 ∧ p5) ∧ (p3 → False))) ∨ p2) ∧ (p3 → (((False → (p2 → p4)) → p4) ∨ p5))) → ((True → False) → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318862083921252662957992452607 : (p4 ∨ (((False → (((((((False ∨ ((p5 → p2) ∨ (p3 ∧ p2))) ∨ p3) ∨ False) ∨ p4) ∧ False) ∨ True) ∧ True)) → False) ∨ (False → (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317356488643307276129780978591 : (p4 ∨ (((((True ∧ True) → True) → (p1 ∧ ((False ∨ (False → p1)) → p2))) ∨ ((p5 ∨ (p1 ∨ (p4 → (p4 ∨ (p4 ∨ p3))))) ∨ p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112338493130040491431413456276 : (((p5 → (((p5 → ((((p5 ∨ True) ∨ (p5 → (p5 → False))) → True) → p2)) → (p3 ∨ ((p1 ∧ True) ∧ p4))) ∧ False)) ∨ True) ∨ (p3 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266074441124446237062484816725 : (True ∧ (p2 → ((((p4 → ((p4 ∧ (p1 → p3)) ∨ ((False → True) → ((False → False) ∧ p3)))) → (p5 ∨ p5)) → p1) ∨ ((False ∧ p1) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147157615284027701416905866825 : (((p4 ∧ ((((((p4 → p2) ∨ p4) ∧ ((p1 ∧ p1) ∨ (p5 → (p4 ∧ p1)))) ∧ p5) ∨ p3) → p4)) ∧ p1) ∨ (True ∨ (p3 ∧ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230670344315143124237740547147 : (((p3 → p4) ∧ p3) → ((((p5 ∧ (p4 ∧ p5)) ∧ (p1 → (((p5 → p3) → p3) ∧ p4))) → ((p1 ∧ False) ∧ (p3 ∨ p1))) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641637897134444106798000437590 : (((((True ∨ p1) → ((p2 ∨ ((p3 ∨ (False ∧ ((p4 ∨ (p1 ∧ (True → (False ∨ (p5 ∧ (False ∨ p4)))))) → p3))) → p4)) → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4616167965054422656876489416 : (p4 → (p3 ∨ (((True ∨ p2) → (((((p4 ∨ p4) ∧ (p4 ∨ True)) ∧ False) ∨ (False ∨ p5)) ∨ p4)) ∨ ((False ∧ False) ∧ (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_134683842082434919793846091800 : ((((p3 → (p4 → (p5 → (False ∧ p2)))) ∧ (p4 ∨ ((p1 ∧ p2) ∧ ((p4 ∨ p5) ∨ (True ∨ (True ∧ p3)))))) → p5) ∨ ((False ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123332026154042821597035988046 : ((((p4 → (p1 → (True ∧ (p2 → True)))) ∨ (((p2 → p3) ∧ p5) → (p1 ∨ (p4 ∧ p1)))) ∨ ((p1 → p1) ∧ (p4 ∧ False))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624532829334793555926302773591 : ((((p4 ∨ ((((p2 → p1) ∨ p5) ∨ (p1 → (p1 → (((((p3 → (p3 ∨ p4)) → (True ∨ p4)) ∧ False) ∧ p2) ∧ False)))) → p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_50417469212603294131992630386 : (((p2 ∧ ((False ∨ ((True → True) → (p1 ∨ ((p3 → p3) → (True ∧ p4))))) ∨ ((p1 ∨ p3) ∧ p4))) ∨ ((p2 ∧ True) ∨ (True ∨ p3))) ∨ p4) := by
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
theorem thm_5_vars_220000406559676401700460156420 : ((p5 → (True → (p3 ∧ p4))) → (p3 ∨ (((p4 ∧ ((p3 ∨ ((p1 ∨ (p5 ∨ True)) ∨ (False ∧ p4))) ∨ p1)) ∧ (p5 → p3)) ∨ (False → p3)))) := by
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
theorem thm_5_vars_344390285185806126451572517636 : (p2 → (p4 ∨ (False ∨ ((((p2 ∨ p2) ∧ (((p3 ∨ (p5 ∧ p3)) ∨ True) ∧ (p5 → (((p2 ∨ p1) ∧ p2) ∧ (p1 → p1))))) ∨ True) ∨ p2)))) := by
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
theorem thm_5_vars_247940391499895107180858607217 : ((p1 ∨ p3) ∨ (p5 ∨ (((p3 ∨ ((p3 ∧ ((False → p2) → ((p1 ∧ True) ∧ (p1 ∧ True)))) → (p2 ∧ (p4 → p2)))) ∧ (True ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56529105012983016843905346231 : (((True ∨ (p3 ∨ (False ∨ p5))) → (((p4 ∨ (p3 ∨ False)) ∨ ((False ∧ True) → (p5 ∧ p3))) ∨ ((p4 ∧ p1) → ((p4 ∧ False) → p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342705642317168806014212289297 : (p2 → ((p5 ∨ (p2 → (p3 ∨ (p2 ∨ (p5 → (p1 ∨ p5)))))) → (p5 → ((((p4 → (p4 ∨ (p5 → p1))) ∧ p5) → p1) ∨ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_213090902944423830373492660344 : ((((p5 ∧ p1) ∧ p1) ∧ p1) ∨ (((p1 ∧ (p5 → ((True → p3) ∧ (True ∨ ((False ∧ p3) → p4))))) → (p1 ∧ ((True → p3) ∨ p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41943966831826762561758987234 : ((((False ∧ False) ∧ (True ∧ (p4 → (p5 ∨ ((((p4 → p1) ∨ (p5 → (((p1 ∨ False) ∨ False) → p2))) → p2) ∨ (p5 ∧ p5)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171365365203942048286572120804 : ((((((p2 → p3) ∨ p1) → (p1 ∧ ((p5 → p4) → p4))) ∨ (True → True)) ∧ p3) ∨ (True → ((True ∧ (p2 ∧ (False ∧ False))) → (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47511400489597425058489193582 : (((p2 ∨ ((((p5 ∧ p3) ∨ True) ∧ p1) ∨ (((True ∨ ((p1 ∨ (False ∨ p3)) ∧ p5)) ∧ (p4 → (p3 ∧ False))) → p5))) ∨ (p1 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244397216968640164083023038883 : ((False ∧ p1) ∨ (((((p5 ∨ p3) ∨ p4) → p3) ∧ p1) ∨ ((((p2 ∨ p2) → True) → ((p2 ∧ (p2 → p2)) ∧ p5)) → (p4 → (True ∨ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299112174873099850497660293512 : (False ∨ (((p4 ∧ ((p1 → (((p3 ∧ p2) ∧ (p5 → (p4 ∨ (p4 → (True ∧ p2))))) ∨ (True → ((p3 → False) → True)))) ∨ True)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147467431804391250447181073628 : (((False ∧ ((((p5 ∨ p4) ∨ (True ∨ (p1 ∨ p5))) ∧ (((p3 ∨ p2) → p4) → p3)) ∨ (p1 ∨ p3))) ∨ p1) ∨ (True ∨ ((p1 ∨ p3) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177503916981703110437230609340 : ((p1 → (p4 ∨ ((p2 ∨ (p5 ∨ (p4 ∨ True))) ∨ ((p2 ∧ True) → False)))) ∧ (p5 → (p3 ∨ ((p5 ∨ (True ∧ ((p2 ∧ p4) → False))) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136030437833401734266033044046 : ((((p3 → (p5 ∨ p2)) ∨ (p3 ∧ ((p3 → p4) ∧ p1))) → (((p1 → p1) ∧ ((p5 ∨ p3) ∧ True)) → (p2 ∨ p3))) ∨ ((p2 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105469450640778376315923341419 : ((((p3 ∨ (False → (p2 ∧ (False ∧ ((False ∧ p4) ∧ p4))))) ∧ (((p5 → p2) → p5) ∨ False)) ∨ ((p4 → (p5 → p5)) ∨ p2)) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112837273018422127562405443536 : (((((p1 ∧ p2) → (p3 ∨ p2)) → ((p5 ∨ p1) → (((p1 ∨ (p5 ∨ p1)) → p3) → (False ∧ ((False ∧ p1) ∧ p1))))) → p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113115358936147799152456876024 : (((False → ((((p2 → True) → p2) ∧ (p5 ∧ p3)) ∧ (((False ∨ (((p4 ∨ (p5 ∨ p3)) → p3) → True)) ∧ p5) ∨ False))) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687290437710103042212514745740 : (((((((((p2 ∧ p1) → p4) → p5) ∧ p3) ∨ (p2 ∧ (p2 → (False ∧ p3)))) ∧ p5) ∧ (((False → (p2 ∧ (p3 ∧ p1))) ∨ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115358812559396559537003418036 : (((((p5 ∧ (True → p2)) ∧ (p4 ∧ True)) ∨ False) ∧ ((p2 → (p4 → ((p3 ∨ (True ∧ p2)) ∧ (p1 ∨ p1)))) ∨ (p1 → p2))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722218168426331161763169138735 : ((((p5 → ((p1 ∨ False) → p4)) → (((True → (p3 → ((p1 ∧ p3) → ((p2 → (((p3 → p5) → p3) → p1)) ∨ True)))) ∧ p1) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185530068444712969990192195163 : ((p3 ∨ ((((p2 ∧ p1) → False) → p2) → (p3 → (p1 ∨ p4)))) ∨ (False → (((p5 → (p5 ∨ p4)) ∧ (p3 → (p3 ∨ (p4 ∨ True)))) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157681673134930092456962203413 : (((p2 ∧ ((p2 → p5) → (((p4 ∨ ((p2 → True) ∧ p1)) → p4) → p1))) ∨ ((False ∧ p4) → p4)) ∨ (p2 ∧ (p1 ∨ (p5 ∧ (True → p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40914380411131749186174041938 : ((((p2 ∨ ((True ∨ ((((p3 ∧ (p3 ∨ p1)) ∨ True) → p5) ∧ (True ∧ (p4 ∨ (p4 ∨ p2))))) → (p2 ∨ p3))) ∧ (True ∧ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354828045901890293881799138508 : (p5 → ((((p3 ∨ p1) → False) → ((True ∧ (True → ((((p1 ∨ (((True → p5) ∨ False) → p5)) ∧ p5) ∨ (p3 ∧ p2)) ∨ p2))) → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46301260104015399804228492844 : ((((((p1 ∨ (p3 → p3)) → (p2 ∨ p4)) ∧ (p1 ∧ (p2 → (p1 ∧ (False ∨ (p3 ∨ p4)))))) → ((p2 → False) ∨ False)) ∧ (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687241961613301544732055869284 : (((((((p2 → (p5 ∨ p2)) ∨ (p3 → (p3 ∧ (False → (p4 → False))))) ∨ p2) ∧ True) ∧ ((p1 ∨ p4) → (((p1 ∧ p1) ∨ p5) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207828745547395046674395243035 : (((p5 → (p5 ∨ (True ∨ p3))) → True) → (((p3 → ((p4 → ((p2 ∧ p4) ∨ p2)) ∨ False)) ∨ (p4 ∧ True)) ∨ (False → (p4 → (False ∧ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113944940727815829105741007335 : ((((((p2 ∧ p5) → True) ∨ p1) → ((p3 ∨ (False → p4)) → (p3 ∨ ((p1 ∨ (p2 ∨ True)) ∨ p4)))) ∧ (p3 ∨ (True → p3))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799930376436953189633444493093 : (((p2 → (((p1 ∧ (((((p1 ∧ p3) → ((p3 ∧ (((p5 ∧ True) ∧ True) ∨ (False ∧ p4))) ∧ p4)) ∨ p4) ∨ p3) ∧ p5)) ∧ True) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326949608179902057962807452523 : (True → ((((((p3 ∧ p4) ∨ ((False ∨ True) → ((p4 ∧ (p5 ∧ p4)) ∧ ((p1 ∧ (p3 → False)) ∨ True)))) ∧ p2) ∨ True) ∨ (False ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118628305324635620256385737135 : ((p4 ∨ ((((False ∧ p3) ∨ p4) ∨ p3) ∨ (False → ((p1 ∨ ((p1 ∧ (p3 ∨ ((p2 ∨ p2) ∨ (p1 ∨ False)))) → p3)) → p3)))) ∨ (p1 ∧ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225947915941715894264021681544 : (((p2 ∧ p4) ∨ p4) ∨ ((p3 ∨ (p2 ∧ ((p2 ∧ True) → p4))) ∨ ((True ∧ False) → (((p2 ∧ (False ∨ ((True ∧ p1) ∧ p3))) ∧ False) ∨ False)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737089031533542887395300760152 : ((((p3 → p3) ∧ ((p2 → (((((True ∨ p4) ∨ (p1 ∧ p1)) → p2) ∧ (((p1 ∧ (p1 → p4)) ∨ p3) ∨ (p4 ∨ p5))) ∨ p2)) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117513509180372697334794632158 : ((p2 ∧ (((((True → p2) ∨ (True ∨ (p3 ∨ (p1 ∨ (False ∨ False))))) ∨ p1) ∧ (((p3 ∧ True) ∨ (p4 ∨ p3)) ∧ False)) ∨ p2)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185199916646804016412155455860 : ((True ∧ ((((p5 ∨ True) ∨ p1) ∨ True) → ((p1 → p4) ∧ False))) ∨ ((False → (((p1 ∧ True) ∧ p5) → p5)) → ((p1 ∨ False) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46980189121278962018610157523 : ((((((p2 ∧ (((p1 → ((((True ∨ p5) ∨ p4) → True) ∨ p5)) ∨ False) → (False ∧ p2))) ∧ False) → (p5 ∧ True)) → p3) ∨ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345061159018524647791464231661 : (p3 → ((((True → (True → ((((p4 → (p5 ∧ p1)) ∨ (p5 → (p4 ∧ p2))) ∨ p4) ∧ p4))) ∧ True) ∨ (p5 ∨ (True → (True → True)))) ∧ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676515007878140933216487448060 : ((((True ∧ (p4 ∧ (False ∨ (p2 ∧ ((((p1 ∨ (p1 ∧ p3)) → (p2 ∨ (p4 → p2))) → p2) → p1))))) ∧ (True ∧ ((p3 ∧ p1) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174552065866513177695054051933 : ((((p3 ∨ (p4 ∨ p3)) ∧ True) ∧ (p3 ∧ ((p4 → (True ∧ p4)) ∨ (p4 → p3)))) → (((p2 → False) ∨ (p5 ∧ (p5 ∨ p4))) ∨ (p3 ∨ p5))) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191268656190798439039134637271 : (((False ∨ False) ∧ ((p2 → (p3 ∨ p5)) ∧ (False ∨ p5))) ∨ ((p5 ∧ ((p4 → ((True ∨ True) ∨ (False ∧ True))) ∧ (p2 ∨ False))) → (True ∨ p2))) := by
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
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261275230647878153582106900137 : ((p5 → True) → (((p4 ∨ ((False ∧ p3) → ((True → True) ∧ ((p4 ∧ p4) ∨ p4)))) ∨ p3) → ((((False ∧ (p2 ∧ p1)) ∧ p4) ∨ True) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
theorem thm_5_vars_259178799052267999416727960559 : ((False → True) → (p2 → (((((((((p2 ∧ False) ∨ True) → p1) ∧ ((p5 → False) ∨ p1)) ∨ False) ∨ True) ∧ p3) ∧ p3) ∨ (p1 → (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157610894996394754880335314476 : (((((False ∨ False) ∨ ((p1 → p5) ∧ (p5 → ((p1 ∨ True) ∧ True)))) ∨ p4) ∧ (p2 → (False ∨ p1))) ∨ (((p5 → p2) ∧ p3) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_984525684286186341436990812155 : (((p1 ∧ (True → (((p4 ∧ (p2 → p2)) ∧ (p5 → p3)) ∧ (((False ∧ (False ∧ (p3 → (p5 → p2)))) → False) ∧ ((True ∨ p4) ∧ False))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_238320336823965387779063592300 : ((False ∨ True) ∧ (((p1 → (True ∨ ((True ∨ ((p3 ∨ p1) ∧ True)) ∧ p1))) → False) ∨ ((((p1 ∨ p5) ∨ (p1 ∧ p3)) ∧ (False ∧ p1)) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198732381377482518579067081367 : ((p5 ∨ (p4 ∨ (((p4 ∧ False) ∧ p3) ∨ True))) ∨ ((p1 ∧ (p5 ∨ (p2 ∧ ((p2 ∧ ((p3 ∧ False) ∧ p2)) → (p4 ∧ (p4 ∨ p5)))))) ∧ p3)) := by
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
theorem thm_5_vars_138396883792262134332317542221 : ((p4 → (p5 ∨ ((p3 ∨ p1) ∧ (((((False ∨ p3) ∨ (((p4 → False) ∧ p5) ∧ (p5 → True))) → p5) ∨ p4) ∧ p5)))) ∨ ((False ∧ p5) → p3)) := by
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
theorem thm_5_vars_303067541720732307362940298730 : (False ∨ (p2 → ((((True → (p3 ∨ True)) ∨ p1) ∧ ((p3 ∧ p5) ∨ p4)) → ((p4 ∧ (((p3 ∧ p4) ∧ (p3 ∨ True)) ∨ p3)) → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h2.left
      let h26 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h2.left
    let h39 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h49 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118263113220750335273093219688 : ((p1 ∨ (((((True ∧ ((p3 → p5) ∨ p3)) ∨ p5) ∧ p4) ∨ (True ∧ p3)) → ((((p3 ∧ p1) ∧ p3) → p2) ∨ (p2 ∨ p1)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115150511072282595262980963985 : (((p3 ∨ ((p1 ∧ (((p2 → p1) ∧ (p1 ∧ p5)) ∨ p1)) → p5)) → ((p5 ∨ False) ∧ (((p2 → p3) → p1) → (False ∧ p1)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341903336875643373638641773029 : (p2 → ((((p4 → p4) ∧ ((p1 ∧ (((p1 ∨ (p5 ∨ True)) → (p1 ∨ p3)) ∨ ((False ∨ p2) ∨ p1))) ∨ True)) ∨ p2) ∧ (p4 → (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305450065560695197684111207828 : (p1 ∨ ((p5 ∧ (((p2 → ((p1 ∨ False) → (False → p2))) → False) → (True ∨ (True → p3)))) → ((True ∧ (p4 → (True ∧ (p3 ∨ p5)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341978469482630535606941432399 : (p2 → (((((((p2 → p4) → p2) ∨ p2) ∧ (((p2 ∨ False) → p3) → (p1 → p1))) → (p4 ∧ p3)) ∧ (True ∧ True)) ∨ ((p3 → p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587992052419704308168016618975 : ((((((p2 → ((p3 ∨ ((((p4 → p3) → (p2 ∨ p1)) ∧ (p3 ∧ True)) ∨ (p3 → p5))) → p2)) → (p2 ∨ (True ∧ False))) ∨ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121382947209455641227594920220 : (((((((p1 ∧ ((False → (((False ∨ p4) ∧ (p1 ∨ True)) ∨ p4)) → p1)) ∨ True) → False) ∨ ((p4 ∨ True) ∨ p1)) ∨ False) → False) → (p4 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∧ ((False → (((False ∨ p4) ∧ (p1 ∨ True)) ∨ p4)) → p1)) ∨ True) → False) ∨ ((p4 ∨ True) ∨ p1)) ∨ False) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((((p1 ∧ ((False → (((False ∨ p4) ∧ (p1 ∨ True)) ∨ p4)) → p1)) ∨ True) → False) ∨ ((p4 ∨ True) ∨ p1)) ∨ False) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102861411813012510690912153233 : (((((p3 ∨ (False ∧ p3)) ∧ (((p3 → p5) ∧ ((p3 → (p1 ∨ p5)) → (False ∧ True))) → (True → p1))) ∨ (p4 ∨ True)) ∨ True) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226878991040715806534386528072 : (((p5 ∧ p2) → p1) ∨ (((p4 ∧ False) ∧ p5) ∨ ((p1 → (p3 → (((p5 → False) ∨ (p1 ∨ p3)) ∨ p3))) ∨ (((p5 ∧ p3) ∧ p1) → True)))) := by
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
theorem thm_5_vars_113486916970324025202411895981 : (((((p4 ∨ (p4 ∧ (((p2 ∧ p2) → (((p5 ∨ p2) ∨ True) → p5)) ∨ p2))) ∧ (p5 ∨ p1)) → (p2 ∨ p5)) ∨ (p2 ∨ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724496790844378274101479133222 : ((((False ∨ (p3 ∧ False)) ∧ ((p4 ∨ (p5 ∧ (((True ∨ True) → ((p2 ∧ (True → p2)) ∧ p2)) ∧ (p4 ∧ p1)))) ∨ ((p5 → p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307508328935025409767071480803 : (p1 ∨ (True → (((((p2 ∨ p5) → p1) ∨ (p4 ∧ (p2 ∧ p1))) → False) → ((((p2 ∧ (p2 → p2)) ∧ (p3 → p2)) → (p3 ∨ False)) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773657855358121582609221561716 : (((False ∨ ((True → (False ∨ ((p1 ∧ True) → (p1 ∧ (p3 ∧ ((((p1 ∧ (True ∨ False)) ∧ True) ∧ False) ∧ ((False ∧ False) ∨ True))))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352251430232569913384704014849 : (p4 → ((p5 ∨ (p2 ∨ (p2 ∧ p2))) ∨ ((p3 ∨ p5) ∨ (True ∨ (p2 ∨ (False ∨ (((p1 → (((p3 → p2) ∧ p5) → True)) → p1) ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722720372113199814156546484888 : (((((p3 → p2) ∧ p3) ∧ (((p3 ∧ p5) ∧ p3) ∨ ((p2 ∧ p5) ∧ (((p1 ∧ (p2 ∨ p5)) ∧ p1) ∧ (p2 ∨ ((p4 → p3) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135750195452614669161296230393 : ((((p5 ∨ p5) ∧ (False → ((((p4 ∨ p5) ∨ p3) ∨ p4) → (p5 ∧ p3)))) ∨ ((True ∧ (p4 → p3)) ∨ (p4 ∧ p1))) ∨ (True → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260123109901359144309102481262 : ((p2 → p1) → (((p2 → (((p4 ∧ (True ∨ p1)) ∨ p3) ∨ False)) ∨ True) ∧ (((p4 ∨ True) ∧ ((True → (p5 ∨ True)) → (p3 ∧ p5))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221394468936904118480263492924 : (((True → False) ∨ True) ∧ (((p1 → (False ∨ ((p2 → p2) ∨ False))) → ((p2 ∨ False) ∨ (False ∨ (((p2 ∨ p1) ∧ (False → p5)) ∨ p2)))) ∨ True)) := by
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
theorem thm_5_vars_357166884959851253035990137307 : (p5 → ((True ∨ False) ∧ (p1 ∨ ((p3 ∨ (p2 ∨ (p3 → (p1 → ((((p4 ∨ (p3 → p2)) → p4) ∧ p2) → p4))))) ∨ ((p4 → True) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (p3 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47295555505429761605129907398 : (((((p5 ∨ p2) ∨ False) ∧ ((p1 ∧ ((((p2 ∨ True) ∨ True) ∧ ((p3 ∧ p2) → ((p3 ∧ p3) ∧ False))) → p4)) ∧ p3)) ∨ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347204274531398560445912399976 : (p3 → ((False ∧ (((p1 → p5) ∨ p4) ∧ ((p5 ∧ (p4 ∧ p4)) ∧ p2))) ∨ (((p5 → (p1 ∨ p5)) ∧ True) ∨ (((p3 → p2) → p3) ∨ p3)))) := by
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
theorem thm_5_vars_148776895253065107358245945394 : (((((True → p1) → False) ∨ (p3 ∨ p4)) ∨ (p4 → ((p2 → p4) ∧ (((p1 ∨ p2) ∨ True) ∨ (p1 → p5))))) ∨ (p3 ∧ ((p3 → p4) ∧ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190245522425977978753000088889 : (((((True ∧ p3) ∧ ((True ∧ p1) → True)) ∧ p4) ∨ False) ∨ (p3 → ((p1 → ((p2 ∧ True) ∧ ((p4 ∧ (p1 ∧ p4)) ∨ p2))) ∨ (p5 → True)))) := by
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
theorem thm_5_vars_157869027023222142621719777767 : ((((True → (False → (((p4 ∧ p1) ∧ p5) ∨ True))) ∧ p1) ∨ (p1 ∨ ((True ∧ (p2 ∧ p3)) ∨ p1))) ∨ (False → ((p5 ∧ True) → (p5 ∨ p1)))) := by
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
theorem thm_5_vars_729591230581007478621483606970 : (((((p4 ∨ p3) ∨ p5) → ((p5 ∨ ((((True → p1) → p2) → ((p2 → p2) ∨ ((p1 ∨ p2) ∨ (True ∨ p1)))) → p5)) ∨ (p5 ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157576211382122472519495746278 : ((((True → p5) ∧ ((p1 ∧ ((((p2 → p5) ∨ p5) ∧ p2) ∧ (p4 → p5))) → p4)) → (p1 ∧ p1)) ∨ (False → (((p2 ∨ p4) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208551180964545898004295873910 : (((p2 ∨ p4) → (False ∧ (False ∧ False))) → (p5 → (((p1 ∧ ((((p2 ∧ p4) → ((p5 ∨ p4) ∧ p1)) → False) ∨ False)) ∨ p3) ∨ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37937325688714085225376399055 : ((((p1 ∨ ((((p4 → p5) → (((((False ∧ p1) ∨ p3) ∧ (p5 ∧ p2)) ∨ (p3 ∧ p5)) ∧ False)) ∨ p4) ∨ False)) ∧ (p1 → False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135572345799069686922282262822 : (((((p2 ∧ (p3 → (p4 → True))) → (p5 → ((True → (False ∨ False)) ∨ True))) ∧ p4) ∨ ((p3 → True) → (p2 ∨ False))) ∨ ((p4 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3036422924519845750255193064 : ((p1 ∨ (p3 ∧ True)) → ((((p4 → True) ∨ (p5 ∧ p5)) → (p1 → p4)) ∨ (((p3 → (False ∧ (p4 ∨ True))) ∨ True) ∨ (p4 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112177435906525332894050314276 : (((p4 ∧ (((True → True) → (((p2 → (p4 ∨ (p5 ∨ p5))) ∧ (p4 ∨ p1)) ∨ p5)) ∨ ((p1 → p5) → (p4 ∧ True)))) ∨ True) ∨ (p1 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



