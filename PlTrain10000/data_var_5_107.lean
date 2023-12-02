variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641503023522795548832165362278 : (((((p1 ∧ True) → ((((p5 → p3) → p4) ∧ p3) ∧ ((True → (p1 → ((True ∧ ((False ∧ p3) ∨ False)) ∧ (p3 ∧ False)))) → p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76465132608066402509805885059 : ((((((((p3 ∨ p2) → ((p3 ∨ ((p5 ∧ p5) ∨ p1)) ∨ p4)) ∨ (p5 → (p4 → True))) ∨ p5) ∨ p4) ∨ ((p3 → p4) ∧ p4)) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p3 ∨ p2) → ((p3 ∨ ((p5 ∧ p5) ∨ p1)) ∨ p4)) ∨ (p5 → (p4 → True))) ∨ p5) ∨ p4) ∨ ((p3 → p4) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198243075529864219663377482422 : ((True ∧ (p5 ∧ (p1 ∨ ((False ∧ p1) ∨ p3)))) ∨ (p4 → ((((p3 → p5) ∧ (p5 → (((p4 ∧ True) ∧ True) ∧ (p5 ∨ True)))) ∨ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782217002561644417061886785956 : (((p3 ∨ (((p5 ∧ (False ∨ (p4 ∨ p5))) ∨ (((p3 ∨ (p4 ∧ True)) → p2) → (True ∧ (True ∨ (True ∧ ((p3 ∨ False) ∨ False)))))) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_884508816298485746963264403 : ((p1 → (((False ∨ p5) ∧ (p2 ∧ (False ∨ (((p3 → (p5 ∨ (((p5 ∧ p5) ∨ p2) ∧ p2))) ∧ p2) → (False ∨ p5))))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39143322916075682994725821300 : ((((p5 ∧ p5) → (((((p3 ∨ p2) → (p2 → p1)) ∨ (p4 → True)) → (False ∨ ((p1 → p3) ∧ p2))) ∨ ((p1 ∧ p5) → True))) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354687323042707010621537030816 : (p5 → (((((((False ∧ (p2 ∨ p3)) ∨ p1) ∧ True) ∧ (p5 ∧ ((p3 → False) ∧ ((False ∧ (p5 ∧ p2)) ∧ p3)))) ∧ p1) ∨ (False → p5)) ∨ False)) := by
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
theorem thm_5_vars_113411894201674364155963862480 : ((((((p2 ∨ (p5 ∨ ((p2 → (((p4 ∧ p4) → p1) ∧ p3)) → (p5 → False)))) ∧ (p5 → p5)) → p4) ∧ p1) ∨ (False → p3)) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124794281396507304809541737439 : (((p4 → (False ∧ (p4 ∧ p1))) ∧ (((p2 → (((((p1 → p1) → p2) ∧ True) ∨ p1) ∧ p4)) ∧ (p4 ∧ (True → p5))) ∨ p4)) → (p2 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h23 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h24 := h16 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h27 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h28 := h16 h27
    -- We need to get the left conjuct of h28 based on <expert-advice>.
    let h29 := h28.left
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148398118881533326383647818703 : (((p2 ∨ (((p1 → ((p2 ∧ p4) ∨ (p5 → True))) → p5) ∨ (p4 → p5))) ∨ ((p5 ∨ (p4 ∨ False)) ∧ True)) ∨ (p2 → ((p2 ∨ p5) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790163659127237773860324501967 : (((p5 ∨ (True ∧ (((p1 → p4) → ((((p4 ∧ (p5 ∨ False)) ∨ (((True ∧ p3) → p1) ∧ False)) ∨ p4) ∨ ((True ∨ p3) ∨ p2))) ∨ False))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806997746674972534176013173823 : (((p4 → ((p2 ∧ (True ∧ ((p2 → (True ∧ False)) → (((p1 ∧ p3) ∧ (((True → p2) → p4) ∧ True)) ∧ p5)))) ∨ (p4 → (p2 ∨ p4)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156592674966968634825294806489 : (((((((p3 ∧ (p4 ∨ (True ∨ p3))) ∨ p2) → (p4 ∧ ((p3 → p1) ∧ p1))) ∧ p4) ∧ p5) ∧ p1) ∨ (p1 → ((True ∨ False) → (False → False)))) := by
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
theorem thm_5_vars_43919690382486991477443674692 : ((((((((p5 ∨ False) → p4) ∧ p3) ∧ ((p4 ∧ False) → (p2 ∨ (p2 ∨ ((p1 → True) ∧ (p2 ∨ p4)))))) → p3) ∨ (p2 ∨ p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112414553107836351012741269347 : ((((p1 ∨ (p4 ∧ ((False → (p1 ∨ (((False ∨ p2) → False) ∨ p4))) ∨ (((True ∧ p4) → (p1 ∧ p4)) ∨ p1)))) ∧ p5) → p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56507971035765796349605183836 : (((p3 ∧ ((p4 ∧ p4) → p3)) → ((((False ∨ p4) ∧ p1) ∧ p3) → (((p1 ∧ p1) ∨ False) ∧ (((False → False) ∧ (True → p4)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211538528960999399975120786579 : (((False ∨ False) → (p2 → True)) ∧ ((False ∧ (((p4 → p4) ∧ True) → (p2 → (((p5 → False) ∨ p3) ∧ p2)))) ∨ ((p4 → True) → (p2 ∨ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_900860866784210450048527056320 : ((((False ∨ (p5 → (((p2 ∧ ((p1 ∨ p1) → (p2 ∨ p5))) ∨ (p5 ∨ p5)) → (((True ∧ p2) → False) ∨ True)))) → ((p5 ∧ True) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p5 → (((p2 ∧ ((p1 ∨ p1) → (p2 ∨ p5))) ∨ (p5 ∨ p5)) → (((True ∧ p2) → False) ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57744420152464899707837603606 : ((((True → p1) → p3) → (((p5 ∨ (False ∨ p3)) ∨ (p4 → p2)) → (((((False ∧ ((p3 → True) ∨ p2)) → p2) ∧ p1) → True) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118736683928865439507447213367 : ((p5 ∨ (((False ∧ p4) → ((p3 ∧ p1) → ((p2 → False) ∧ False))) ∧ (p1 → (((p3 → (p2 ∧ (p1 ∧ p3))) ∧ p2) → p5)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198166807064257049427157612192 : (((p2 ∨ False) → ((p3 → False) → (False ∨ p4))) ∨ (((((((p5 → False) ∧ p2) ∨ False) ∨ p3) → p5) ∧ False) ∨ ((p3 ∨ (p1 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164794166266594966328423748407 : (((((p5 ∨ p2) ∨ (p3 ∨ p4)) → (((p4 ∧ False) ∧ True) ∧ ((True ∨ p1) → p1))) ∨ True) ∨ ((p2 ∧ False) ∧ (((True ∨ p5) ∧ False) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656399936462311831877304318563 : (((((((p5 ∨ p2) → (True ∧ (p1 → (p1 ∧ False)))) → False) ∧ ((True → ((p2 ∨ (p3 ∨ (p1 ∨ True))) → p1)) ∧ p3)) ∨ (p2 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_310399773808029520597226290545 : (p2 ∨ (((p3 ∨ p5) ∨ (p2 → (p5 ∨ (p4 ∨ True)))) ∨ ((p2 ∨ (((p1 → (True → p1)) ∧ False) ∨ (True ∨ (True ∨ False)))) ∨ (p5 ∧ p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213514422393576712458160600825 : (((p4 → (p3 ∨ p1)) ∧ True) ∨ (p1 ∨ (((((p3 → (p4 ∧ p5)) ∨ p2) ∨ (p1 → p1)) → (((p3 ∧ p5) ∧ (p3 ∧ p4)) ∧ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → (p4 ∧ p5)) ∨ p2) ∨ (p1 → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158770364106003519822529446155 : ((p4 ∧ (p5 ∧ ((p4 ∧ (True ∧ (((p5 ∧ (p3 ∧ (p3 → p3))) ∨ (p1 → True)) ∨ p4))) ∨ True))) ∨ (False → (((True ∧ p4) ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610711593658913465528362865088 : (((((((p5 → (p2 ∧ p2)) ∧ ((True ∨ (p1 → p2)) ∨ (False ∨ (((False → p5) → False) ∨ p2)))) ∨ (p5 ∨ (p3 ∨ p3))) → False) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_745218082717710317969886726667 : ((((p5 ∧ True) → ((True ∨ p2) → (((p3 ∧ (p2 ∨ (p2 → ((p5 ∧ (p2 ∧ p5)) ∨ p1)))) → (((False ∨ p5) → False) → p1)) ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157761605454648775604639738033 : (((p1 ∧ ((False ∧ (p4 ∧ p3)) ∧ ((False ∧ (p1 ∨ p1)) ∨ False))) ∧ (True → (p5 → (p5 → p1)))) ∨ ((False ∨ (False → p1)) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42591178557656748204193717499 : (((p2 ∨ ((p1 ∨ p1) ∨ ((p2 ∨ p4) ∨ (((((p1 ∧ (True ∨ (p4 ∨ True))) ∨ (p1 → (False → p3))) → p2) → True) → True)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183927855490440920655403938036 : (((p4 ∧ (((p2 ∨ (p3 ∧ p1)) → (p2 ∧ p2)) → False)) ∧ p5) ∨ (((False ∧ p1) ∨ (False ∧ (p5 ∨ (p3 ∧ p5)))) → ((True ∧ p4) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234742916044576806529201214452 : ((p4 → (False → p5)) → ((((p2 ∨ (False ∨ (p4 → ((((False → True) ∧ ((True → p4) ∨ p4)) → (p4 ∧ False)) → p4)))) ∧ False) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171496615327063485646400847095 : (((p4 → ((p4 → (p1 ∨ (p2 ∧ (p3 ∧ ((p2 ∨ p2) → p3))))) ∧ False)) ∧ True) ∨ (((p5 ∨ (p1 → p4)) ∧ p5) → ((False ∨ p1) ∨ True))) := by
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
theorem thm_5_vars_799245987934922116913555970697 : (((p1 → (p3 ∧ ((((p3 ∨ p4) ∨ ((p5 ∧ (False ∧ ((p2 ∧ True) → (p2 → ((p4 ∨ False) ∧ True))))) ∨ (p1 ∧ p1))) ∧ p3) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317753176201931460660895826265 : (p4 ∨ (((((p4 → p5) ∧ (p5 ∧ (False ∨ ((False → ((True → (p5 ∧ True)) ∨ True)) ∨ p2)))) → p3) → (False ∨ (p5 ∧ (True → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338635775760669923943333285289 : (p1 → ((True ∧ p1) ∧ ((((True → (p2 ∨ (p4 → (p1 → ((p4 ∧ False) ∨ False))))) ∧ p3) ∧ (False → (p5 ∨ p3))) → ((p5 → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60202387404786665396782393543 : (((p5 ∨ p5) → (((p2 ∨ p5) → p5) → ((p2 ∨ (((p1 → p1) → (p3 ∨ ((p5 ∧ True) ∧ (p3 ∧ (p1 ∧ p3))))) → p1)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697535070861241474179987177033 : ((((p5 ∧ (p1 ∨ (((p5 → (p1 ∧ p1)) ∧ (False ∨ True)) ∨ p5))) ∧ ((p2 ∨ ((True ∧ p5) ∧ (((p2 → p1) ∧ p4) ∧ p5))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329021386669688101604684693078 : (True → (((((p4 ∨ p3) ∧ p1) ∨ True) → False) → (p2 → (p5 ∧ (p3 ∨ ((((p2 ∨ (p4 ∨ p4)) ∧ ((p1 ∧ p2) → p5)) ∧ p3) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ p3) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 ∨ p3) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340293628593687216593350561226 : (p2 → (((p2 ∧ (((p1 ∧ ((p3 ∧ p5) ∨ False)) ∧ p2) ∨ ((((p3 → p3) ∧ (p3 → False)) ∧ (p2 ∨ (p3 → p3))) ∨ True))) ∧ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51388756510373902197865979992 : (((((p2 ∨ True) → (p4 ∧ (((p2 ∨ (p5 → ((p4 ∧ p1) → p2))) ∨ p2) ∧ p1))) ∨ p1) → (((p2 ∨ (True → p2)) → p1) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p2 ∨ True) := by
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
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174453865391230006630984289431 : (((p2 ∧ ((p3 ∨ (False ∧ (False → p5))) → p5)) → (p2 ∨ (p1 ∨ (False ∨ p1)))) → ((p5 ∨ ((p2 ∨ (True → (True → False))) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206349842596838534353607437680 : ((p2 ∨ (((p1 ∨ p5) → p5) → p1)) ∨ ((((p3 → p5) ∧ False) ∨ True) ∧ ((((False ∧ p2) ∨ p3) ∧ (p3 ∨ p1)) → (p3 ∨ (False ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745287337772103684493655048091 : ((((p5 ∧ p1) → ((False ∨ (((p2 ∧ p3) → p1) → (True ∧ ((p1 ∧ False) → (p3 → False))))) → ((((p3 ∨ False) ∧ p5) ∨ False) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341809333125472291434901010041 : (p2 → ((((((p5 ∨ (p1 ∨ False)) → ((True ∨ p3) ∧ (False → p1))) ∨ p2) ∨ ((p5 ∧ (p2 ∨ p3)) ∨ p4)) ∧ (True ∨ p4)) → (p1 ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216427680411740731789995025443 : ((p4 → ((p3 → False) ∨ p2)) ∨ (p4 ∨ ((p1 → ((p3 ∧ ((p4 → p3) ∧ ((p2 ∨ ((p2 ∧ (p3 → p1)) → p2)) → p2))) ∨ p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_56157222672932114067785453695 : (((True ∧ (p2 ∧ (p1 ∧ p3))) ∨ ((p1 ∧ p4) ∧ ((((p4 ∧ p3) → p2) ∧ (p4 → (((p1 ∧ True) ∧ (p1 ∧ True)) ∧ False))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50053808863179038845211775407 : ((((p5 ∨ True) ∧ (((((p5 ∧ ((True ∨ (True → (p5 ∧ p5))) → False)) ∧ p4) ∧ p4) ∧ p1) ∨ False)) ∧ ((p2 ∨ p3) ∧ (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58908460233247729995741193931 : (((p1 ∧ True) ∨ (((True → (False → p4)) ∧ ((False ∧ p1) ∧ p1)) ∨ ((((False → False) → (p1 ∨ True)) ∧ (True → p4)) ∧ (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47571598035842453490756351590 : (((p1 → (((p5 ∨ (((p5 ∨ True) ∧ ((p3 ∨ False) ∨ p1)) → (((p2 ∧ p3) ∨ True) → False))) ∧ (p5 → True)) ∧ False)) ∨ (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122077123967050329486062108665 : (((p3 → ((p3 → p4) ∧ ((((p5 ∨ p5) ∨ p5) ∨ False) ∧ (p1 ∧ (((p5 ∨ False) ∧ (p1 ∨ p5)) → (True → p3)))))) → p1) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786415673623403730747385839770 : (((p4 ∨ ((((p1 → (((p3 ∨ p2) → ((p3 ∨ False) ∨ False)) ∨ p4)) → p1) ∨ p3) ∨ ((True ∨ p5) ∨ (p1 ∧ ((p5 → p5) ∧ p3))))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_48389290028233387539885125197 : (((False → (((((p2 → (False ∧ ((p3 ∨ p3) ∨ ((True ∧ p5) ∧ p3)))) → (True ∨ False)) → p3) → (True ∨ p1)) → False)) → (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314081133624050628938300509094 : (p3 ∨ ((((p3 ∧ (((p3 ∧ p5) ∨ (((p3 ∨ p4) ∧ True) ∨ ((p5 ∨ p5) ∨ p3))) ∨ p3)) ∨ p4) ∨ ((p1 → p1) → p1)) → (p5 ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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
          exact h9
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Disjunctions on the left can always be decomposed.
              cases h17
              case inl h18 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h18
              case inr h19 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h19
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h21 =>
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
theorem thm_5_vars_729103224166832151076651661975 : (((((True → p4) ∧ True) → (((True ∧ (False → (p4 ∨ p2))) → ((False ∨ p5) ∧ False)) ∨ (True ∨ (True → (p3 → ((p3 ∨ p2) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63984239062405103668929771278 : ((False ∨ ((((p5 ∧ p4) ∧ False) → (((p5 ∨ p3) → ((p3 ∨ p1) ∧ p3)) ∧ (((p4 → ((False → p2) → p1)) → False) ∨ p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348187230867092553917898331011 : (p3 → ((p4 ∨ p3) → ((p1 ∨ ((p3 ∧ (p2 → p1)) ∧ (p2 ∨ p2))) ∨ (p5 → ((p4 → True) ∨ (False ∨ ((p5 ∧ (True → True)) → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677615714881095316961737030677 : (((((((p3 → False) ∨ (p4 ∧ ((True → ((p3 ∨ (p5 → p4)) ∧ p5)) → (True ∨ p1)))) ∨ p1) → p3) ∨ (False ∨ (p5 ∧ (False ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38554649609585437876356849481 : ((((p5 → (((p2 ∧ p5) ∨ True) → (p4 ∨ (p3 ∧ True)))) ∧ ((((p5 ∧ (p2 ∧ p3)) ∨ (p2 ∧ p1)) → p5) ∧ (True → False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157010269401923818578029680089 : ((((p1 ∧ (False ∧ p5)) ∨ ((p5 ∧ p1) ∨ ((False ∨ False) → ((p3 ∧ (p5 → p3)) ∨ False)))) ∨ p5) ∨ (True → ((p1 ∧ p2) → (p3 ∨ True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47590075757742198186023563284 : (((p2 → ((p3 ∨ p5) → ((False ∨ (p5 ∧ p1)) ∨ ((p2 → ((p2 ∨ p1) ∨ (((p1 → False) ∨ p4) → False))) ∨ p3)))) ∨ (p1 → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341042052021260702271620343659 : (p2 → ((False ∨ ((p3 ∨ ((((((p5 ∧ p2) → True) ∨ ((p5 → p5) → True)) ∨ ((p2 ∨ p3) ∧ (p5 → p2))) ∧ p4) → False)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61095354728390697314489548694 : ((False ∧ ((p3 → (((((((p4 → p1) → (True ∧ p2)) → True) ∨ True) ∧ p1) ∧ p2) → False)) ∨ ((True ∨ (p4 ∨ p1)) → (p1 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57496400770816963221859147968 : (((p2 → (p5 ∧ True)) ∨ ((((True ∨ (p5 → (p3 → True))) ∧ p4) ∨ p4) → ((True → (False ∧ True)) ∨ (p5 ∧ (p1 ∨ (p5 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609575503696825426748051559789 : (((((p4 ∧ ((((p2 ∨ True) ∧ p5) ∧ p3) ∧ (p1 ∧ ((p4 → ((p1 → p2) → ((p2 → True) ∧ p5))) ∨ (p4 ∧ p3))))) ∨ True) ∨ p1) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_245540428150144791382201344848 : ((p3 ∧ True) ∨ (((p5 → ((True → (p2 → (p3 ∧ (p1 ∨ p1)))) ∧ p1)) ∧ ((((False → p5) ∧ p4) ∨ p4) ∧ True)) ∨ ((True → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115984548881755160970551822293 : ((((p1 ∨ (False ∨ True)) ∨ p5) → (((p4 → ((((p5 → p4) ∨ (False ∧ p1)) ∧ (p2 ∧ p2)) → True)) ∧ (p3 ∨ True)) → p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78541699823028739340564890990 : (((((p2 → True) ∨ (p5 ∧ (((((p2 → p3) ∨ p3) → False) → (True ∧ (((True ∧ False) ∧ p1) ∨ p4))) ∨ p4))) → p4) ∧ (p1 → p5)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 → True) ∨ (p5 ∧ (((((p2 → p3) ∨ p3) → False) → (True ∧ (((True ∧ False) ∧ p1) ∨ p4))) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749033817551541154844632834112 : ((((p4 → p5) → ((False ∧ p3) ∧ ((p2 → (False → (True → p3))) → (((p3 ∨ (False ∨ p3)) → ((False ∧ (False → p2)) ∨ False)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641846063504007119091710783155 : (((((False → p1) → (False → (False → ((p5 ∧ (False → p3)) ∨ (((True → (p5 → p5)) ∧ p5) → (((p3 ∧ True) ∧ p3) → True)))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213361365255484643565509627990 : (((p4 ∧ (p5 ∨ p3)) ∧ p3) ∨ (True ∧ (p1 → ((p3 ∧ p3) ∨ ((((((False ∨ p4) → p4) ∨ False) ∧ p5) → (p4 → True)) → (True ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159846064249941248515210731164 : (((p1 → (((p4 → False) ∧ p5) → (p5 → ((True → (p5 ∨ ((p2 ∧ p5) ∧ True))) ∨ p3)))) ∨ p4) → (True ∧ ((False ∧ p5) ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_791567914545661514048094819638 : (((True → ((((p2 → (p3 ∨ (((p1 ∧ (((p3 ∨ p4) ∨ (p4 ∨ p2)) ∨ (p5 ∨ p4))) ∧ (False → p4)) ∧ p3))) → True) ∨ p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40528683534848264696997089257 : ((((p1 ∨ (((True ∨ ((False ∧ ((p1 → p3) ∧ p1)) ∧ ((False ∧ p1) ∧ (p5 ∨ (p1 ∧ (p3 → p2)))))) ∧ False) ∧ p4)) ∨ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725403378875627852002666709128 : ((((p4 → (p4 → p5)) ∧ (p5 ∧ (((p3 → (p5 ∧ False)) → ((p1 ∧ p2) ∧ True)) ∧ ((((p5 ∨ (True ∧ p1)) ∨ False) → False) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228410307618760657112609309787 : ((False ∨ (p1 ∧ p3)) ∨ (p4 ∨ ((p3 ∧ (((p3 ∨ True) ∨ p4) → False)) ∨ (((p5 ∧ False) ∧ (True ∧ ((p3 → p3) ∧ p4))) → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347273493579860197432972357353 : (p3 → ((((p5 ∧ (p1 ∨ p1)) ∨ (p5 ∧ (p3 → True))) ∧ p2) ∨ ((p1 → p4) ∨ (p3 ∧ (((p2 ∨ False) ∨ (p5 ∧ p5)) ∨ (p2 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167293606642238822197673077524 : ((((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) → False) → ((p1 ∧ (p5 ∧ (p4 ∧ p3))) ∧ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h10
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h14
  -- False on the left can always be used.
  apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : ((p3 → (p2 → (((p1 → (False ∨ (p5 ∧ (p4 → p4)))) → p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h19
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191573599558785299343697028904 : ((p2 ∧ ((p5 ∧ ((p5 ∨ p1) ∨ (p3 → True))) → p1)) ∨ ((False ∨ (p4 ∨ (((True ∧ (p4 ∧ p5)) → False) → (p3 ∧ (True → p2))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661301594422258585151902680932 : ((((((False → (p2 → ((p4 ∧ (p5 ∧ True)) → (((((p5 → p4) ∨ False) → p4) ∧ p2) ∧ p5)))) ∨ p4) → (p3 ∨ p5)) → (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322529629870710334462988539536 : (p5 ∨ ((p3 ∧ ((False ∧ p4) ∨ ((True ∧ (((p1 ∧ (p4 ∧ (False ∧ (p1 ∧ False)))) ∨ (p2 ∧ True)) ∧ False)) ∧ ((p2 ∧ False) ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680612508149659922074362486544 : (((((p5 → ((p5 ∨ (p5 ∧ (False → p5))) ∨ False)) → (p4 ∧ ((False ∨ (p4 ∧ p5)) ∨ (p4 ∨ p3)))) → ((p5 ∧ (p5 → False)) → False)) ∨ p4) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350135959719413232457773938866 : (p4 → ((((((((p3 → p5) ∨ p4) ∨ (p2 → True)) ∧ p3) ∧ p3) ∧ (p3 ∨ True)) → (False ∧ (p4 ∨ (True ∧ (p4 → (p4 ∨ p2)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60128063364669901063861190415 : (((p4 ∨ True) → ((p1 → ((((p5 ∨ ((p4 → False) → p3)) ∧ p5) → p4) ∧ ((p5 ∨ p3) ∨ p5))) ∧ (p1 ∨ ((p4 ∧ p5) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173662294929213919278013593987 : ((((p2 ∨ ((p2 ∨ (p1 ∧ (p2 ∧ (p5 ∨ (p5 ∧ p4))))) → p5)) ∧ p3) ∨ p2) → (((True ∧ (p5 ∧ p5)) ∨ p5) ∨ (p4 ∨ (p5 → p5)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778245055353076564634248847021 : (((p1 ∨ ((p3 → p2) → ((((p4 ∨ p5) → (((p4 → True) ∧ (((p4 ∧ (p5 ∨ p5)) → p1) ∧ p1)) ∧ p4)) ∨ True) ∧ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754882743750649296461490908670 : (((False ∧ (p3 ∨ (((p4 → (p3 ∧ ((((True → (p2 → p4)) ∨ p2) → p1) ∧ (p2 ∨ (p3 ∧ p1))))) ∨ (p2 ∨ (p1 ∨ True))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224301958335198070796771560154 : ((False → (True ∨ True)) ∧ ((((p3 ∨ p3) ∧ p3) ∨ True) ∧ ((p3 ∨ (((p1 ∧ p2) ∧ p4) ∧ (True ∨ (p1 ∧ p3)))) ∨ ((False ∧ p4) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_50487131449190245698383156489 : (((p4 → (((p5 ∨ p3) ∧ (((p2 ∧ ((True → p1) ∨ p1)) → p3) → (True ∧ (p4 ∧ p2)))) ∧ p3)) ∨ (p4 → (p2 → (p5 → p2)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351773887973694638628842246747 : (p4 → ((p5 ∨ ((((((p3 → p4) ∨ False) → p3) ∨ p5) ∨ p1) ∨ (p2 ∨ True))) → ((((p5 → p1) ∧ (True ∧ (p5 ∧ True))) ∨ p4) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168711281406182984133701716148 : ((True ∨ (((((p3 ∧ p2) ∧ p5) ∨ p1) → p1) ∧ ((((p2 ∨ False) → p1) → p5) ∨ p3))) → ((p1 ∨ (((p3 ∧ True) → p3) → p1)) ∨ True)) := by
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
theorem thm_5_vars_161592864130255950503610188963 : ((True ∨ (True ∨ ((p3 ∧ (((p2 → (True ∨ (((p4 → False) ∨ p2) → p3))) → p4) → p3)) → p3))) → (((p1 ∧ p2) → (True ∧ False)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125532142555410959796236885224 : (((True → False) ∧ (((((p3 ∧ (True ∨ (p4 → True))) ∨ ((p3 → p5) ∧ (p2 → p2))) ∨ (p1 ∨ (p1 ∨ p5))) → p1) ∧ p5)) → (p5 → False)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322279602961010310437439594676 : (p5 ∨ (((((((p4 ∨ p4) ∧ (p1 → (p3 → (p2 → (True ∧ False))))) ∨ (((p3 → p3) ∨ p5) ∧ (p5 ∧ p4))) → True) ∨ p2) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203469805147247669552602819358 : ((True ∨ ((p2 ∧ p3) ∨ (p2 ∧ p1))) ∧ (((p1 ∧ ((p1 → ((p5 → p3) ∧ p2)) ∨ p1)) ∧ ((p3 → (p1 → p2)) ∨ p4)) ∨ (False → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118290209929428693689098924617 : ((p1 ∨ ((True → p5) → ((p5 → True) → (p2 → (((True → (True ∧ p2)) ∧ p5) ∧ (False ∨ ((p4 ∧ (True ∧ p5)) ∧ p4))))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722549750377187874135273323366 : (((((p3 ∨ p5) ∧ False) ∧ (((p2 ∨ ((p5 ∧ False) ∧ p2)) ∨ (p1 ∨ p4)) ∧ ((True ∨ ((True → False) ∧ p2)) → ((p3 → True) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595235228575840104390636081325 : (((((p2 ∨ ((((p5 → p4) ∨ (p4 ∧ False)) ∧ (p4 → True)) ∧ (p1 → p5))) → ((((p5 → (p4 ∨ p4)) ∧ p1) ∨ p4) → False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63953518974884188421856133450 : ((False ∨ ((p1 ∨ ((p2 ∧ ((p2 → p5) ∧ (((p4 ∨ (p5 → True)) → True) → p3))) ∨ (p4 → (((False ∨ p5) ∧ p5) → p4)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625082288327566767924006931129 : ((((True → ((((False ∧ ((p4 ∧ p1) ∧ p5)) ∨ False) → (p3 → (((p5 ∧ (p5 ∧ p2)) ∧ (True ∨ p3)) ∧ (p2 → p4)))) → False)) ∨ True) ∨ False) ∧ True) := by
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



