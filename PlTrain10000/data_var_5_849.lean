variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322459132120119996913584148616 : (p5 ∨ ((((p3 ∧ p5) ∨ p2) ∨ ((p2 ∨ (p3 → p1)) → ((((p5 → ((False ∨ (p3 → p5)) → (True → p3))) ∧ p3) ∧ p4) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685801241745356107193044642966 : ((((((p5 ∨ ((True ∨ ((p3 ∨ p3) ∨ (True ∨ p1))) ∨ (p1 ∨ p5))) ∨ (True → p5)) → False) → (p3 ∧ ((p2 → (p1 → p3)) ∧ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((True ∨ ((p3 ∨ p3) ∨ (True ∨ p1))) ∨ (p1 ∨ p5))) ∨ (True → p5)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∨ ((True ∨ ((p3 ∨ p3) ∨ (True ∨ p1))) ∨ (p1 ∨ p5))) ∨ (True → p5)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∨ ((True ∨ ((p3 ∨ p3) ∨ (True ∨ p1))) ∨ (p1 ∨ p5))) ∨ (True → p5)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134366697074827900056788984775 : (((p1 ∨ (True → ((p2 ∨ False) → (True ∧ ((True → (False ∨ ((True ∨ (p1 → (p5 ∨ p4))) → p1))) → False))))) ∨ p3) ∨ (False → (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248231090449302227534244711006 : ((p2 ∨ p1) ∨ ((p1 ∨ p5) ∨ (((p3 ∨ (p2 ∨ (p2 ∨ (((True ∨ (p1 ∨ p2)) → ((True ∨ p3) → p5)) ∨ (p1 ∨ False))))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350025651152340210848396977367 : (p4 → (((((((True ∨ False) → ((((p1 → (p5 ∨ True)) → p1) → (p3 ∧ p2)) ∧ p4)) → (True → p2)) → p1) ∨ (p1 → p3)) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173730547636903399193378211603 : ((((p4 ∨ (True ∧ (True → (False ∧ (p5 ∨ p2))))) ∧ ((True ∧ p3) ∨ p2)) ∨ True) → (((p5 ∧ p5) ∨ (p3 → (p5 → True))) ∨ (True ∧ p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h17 := h12 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h21 := h12 h20
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757950101362924668985102701112 : (((p1 ∧ (p5 ∨ ((((p5 ∨ ((((True → (p3 ∧ p5)) ∧ (p4 ∨ p4)) ∧ p4) → p1)) ∨ p2) ∨ (p1 ∨ False)) ∧ (p4 → (False → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191143670253539993827297748469 : ((((False ∨ p4) ∨ p1) ∨ (p2 → ((p5 → True) → p3))) ∨ ((p1 → (((p4 ∨ p2) ∨ (True ∧ False)) ∧ (p5 ∧ (p1 ∧ True)))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151074964067978484473571367566 : (((((((p2 → False) → p2) ∨ False) ∨ ((((p2 ∨ p2) ∨ p4) ∧ False) → ((p5 ∨ p3) ∧ p2))) ∨ True) → p3) → ((p3 ∨ (p5 ∨ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 → False) → p2) ∨ False) ∨ ((((p2 ∨ p2) ∨ p4) ∧ False) → ((p5 ∨ p3) ∧ p2))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213619374046542616427090979520 : ((((p2 ∧ False) ∨ False) ∨ p5) ∨ (((p4 ∧ False) ∧ p1) ∨ (((p3 ∨ p2) ∧ ((((True ∨ False) ∧ (p1 → p1)) ∨ False) → (p4 ∧ p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40723830130791032010435684104 : (((((((p2 ∨ p1) → True) ∧ (p2 ∨ p2)) ∨ ((p1 → ((p1 → ((True ∨ ((p2 ∧ p4) → p1)) ∧ True)) ∧ p5)) → p5)) → p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264059480581174752358075992730 : (True ∧ (((p5 ∧ ((False ∧ (p3 → p5)) ∧ (p3 ∨ True))) ∧ True) ∨ ((p2 ∨ (((p5 ∨ (p4 → p4)) ∨ (p2 ∧ (p1 ∧ p2))) ∨ False)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300368032082201253817588003800 : (False ∨ (((((p2 ∨ p4) ∨ p2) → (((((p3 ∨ p3) ∨ p5) ∨ (((False ∨ p4) ∧ p4) → p5)) → p4) ∧ True)) → p5) ∨ ((p3 ∧ False) → p2))) := by
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
theorem thm_5_vars_136892848773275854181261523069 : (((p3 ∨ p4) ∨ (True ∧ ((False → (((False ∨ True) → (p3 ∨ p4)) ∨ p4)) ∧ (((p2 ∧ p1) ∨ p1) ∨ (False ∨ p2))))) ∨ (False → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656175153151951396155544841993 : ((((((False ∨ p2) ∧ ((((p3 ∨ p3) ∨ p1) ∨ (p2 → False)) ∨ (True ∧ False))) ∨ ((((True → True) ∧ True) → p2) ∧ True)) ∨ (True ∨ p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_587359007610797311286716873778 : ((((((p5 ∧ ((True ∧ p4) → ((((p3 ∧ (((p5 → p3) ∧ (False → p2)) ∧ p1)) ∧ False) → p3) → (p2 ∧ p3)))) ∧ True) ∨ True) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192147305663404146400545400213 : ((p5 → (p4 → (p1 ∨ (((p2 → p1) ∨ p3) ∨ False)))) ∨ ((p4 ∨ ((False ∧ (p2 ∨ (p4 ∧ p5))) ∨ True)) ∨ ((p5 ∨ p2) ∧ (p4 ∨ p5)))) := by
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
theorem thm_5_vars_201078437909570114233061973772 : ((p5 ∨ ((p1 ∨ p4) → ((p2 → p2) ∧ p5))) → ((((((p4 ∨ p4) ∧ p2) ∨ p4) ∨ p3) → p2) ∨ ((False ∨ (p4 → p5)) ∨ (p4 ∨ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779241796355244070320160994319 : (((p2 ∨ (((p1 → ((True → p4) ∨ False)) ∨ ((p3 ∨ p2) ∧ (((False ∨ False) ∨ p1) ∨ (p5 → ((p1 ∧ (p4 ∨ p3)) → p3))))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168650900083253352348586414319 : ((p4 ∧ ((p2 ∧ p4) ∧ (True ∨ (p4 ∧ (True ∧ ((p2 ∨ p4) ∧ ((p2 ∧ p4) ∨ p3))))))) → ((((False ∧ p3) ∧ p2) ∧ p2) ∨ (False ∨ p4))) := by
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
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350135393950394280481780231551 : (p4 → ((((((p1 ∧ ((True ∧ (True ∧ (False → p5))) ∧ p1)) ∨ False) → p3) ∨ p5) → (p5 ∧ ((p2 ∨ (p2 → p2)) ∨ (p1 → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256699405080641960434027261842 : ((p1 ∨ p1) → (((p4 ∧ (((False → (p1 → (False ∧ ((((p2 → (p3 → p5)) ∧ p4) → p5) → p5)))) ∨ p5) ∨ True)) → (p5 ∧ True)) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314406977281607368496874275241 : (p3 ∨ ((((True → (False ∨ p2)) ∨ ((p4 ∧ p2) ∧ ((False → (p1 ∧ True)) ∧ ((p4 → p4) ∨ p2)))) ∨ False) ∨ (((p4 → p4) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54660226617094222464709562669 : ((((False ∧ (((False ∨ p2) ∨ False) ∨ p5)) ∨ p4) → (p1 → ((p4 ∨ p4) → ((True → (((p5 ∨ (False ∧ p5)) ∧ p3) ∨ p1)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2000721891210456901521993766 : (((p1 ∧ (p2 ∧ ((p2 ∨ (((p2 ∨ p1) ∨ True) → True)) → (p3 → p4)))) ∧ ((p3 → p1) ∨ p5)) → ((p4 → False) ∨ (False → p2))) := by
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
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112545931616864563970145819293 : ((((((p3 → p4) → (p4 → (False → p1))) → ((p1 ∧ p2) → (p3 → ((p4 ∨ p2) ∨ ((True → False) ∨ p1))))) → p2) → p2) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315750386349558644975440122434 : (p3 ∨ ((p5 → False) ∨ ((((p1 → p1) → ((p5 → True) ∧ False)) → False) ∨ (((p3 ∨ p4) ∧ (p5 → ((p5 → (p5 ∧ True)) → p4))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117166754603604034032387657740 : ((True ∧ (((((p3 ∧ (True ∨ ((p5 ∨ (((p4 → p5) ∧ p5) → (p2 → p3))) ∨ p3))) ∨ p3) → (p5 ∧ p1)) ∨ p1) → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164442578750163468540642158266 : (((((True → (((p4 ∧ False) → p3) → (True ∧ ((p2 ∨ p4) ∧ True)))) ∧ p3) ∧ False) ∧ p4) ∨ (p5 → (((p1 → (p5 ∨ True)) ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264985608687117440728885326025 : (True ∧ ((True → p5) → (p5 → ((p2 ∨ (True → ((p3 ∨ p3) → (p1 → p4)))) ∨ (((p4 → p1) ∧ ((False ∨ p5) → (p5 ∧ p5))) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117544820558896360598431120238 : ((p2 ∧ ((True ∧ ((p4 ∧ p1) → ((((((p5 → False) → (p1 → p4)) ∨ p4) → p1) ∧ p5) → p1))) → (True ∧ (False ∧ p3)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134926693126298276646404040177 : ((((((p5 → (p3 → p2)) ∨ ((p4 ∨ ((p4 ∨ (p3 → p2)) → (p3 ∨ p4))) ∧ True)) → False) → p3) ∧ (p1 ∨ p5)) ∨ ((p5 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804656586375733065976724355906 : (((p3 → (((True → True) ∧ (p5 → p1)) → (((((((False ∧ p1) → p4) ∧ True) → p1) → (False ∧ p4)) ∨ p3) ∧ ((True → p5) → True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190310904051929585874275610401 : (((((p2 → (p1 ∨ p3)) ∨ p4) ∧ (p3 ∧ True)) ∨ p3) ∨ ((False ∧ (p5 → (p5 ∧ (((p3 ∨ (p4 → p5)) ∨ True) → p4)))) → (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556436028827000059945888143393 : (((p3 ∨ ((((p2 ∨ p2) ∨ (True → (False ∧ (p1 ∧ (p3 → (False ∨ (True ∨ ((p2 ∧ p5) ∨ (p1 ∧ p1))))))))) ∧ True) ∨ (True → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_54821975231473046345165943951 : (((True → ((p2 ∨ (False ∧ p3)) → (False → p2))) → (p1 ∨ (((p3 ∧ (p3 ∧ True)) ∨ (False ∨ ((p3 ∨ p5) → p4))) ∨ (False → p2)))) ∨ p4) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735094988936110441591421830424 : ((((p3 ∨ p1) ∧ ((((False ∧ (p3 → False)) ∧ p5) ∧ (p5 → p4)) ∨ ((p5 ∧ True) ∨ ((p1 → p3) ∧ (True ∧ (p3 → (p2 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1801126411188394863740862528 : (((p5 → p5) ∧ (((p3 ∨ True) → p2) ∧ (((p1 → p5) → ((p1 ∨ p1) ∨ (p1 ∧ (p5 → p4)))) → p5))) ∨ (False → (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39192796593442906313625890577 : ((((p5 → p1) → ((p5 ∨ True) ∧ ((((p2 → True) ∨ (p2 → p1)) ∨ (p4 ∨ (p5 ∧ (p1 → p1)))) ∧ (p5 ∧ (p1 ∨ True))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203706380242750894682928274389 : ((p4 ∨ ((p1 ∧ p3) → (False ∨ True))) ∧ (((p4 ∧ (True ∧ (True ∧ (p5 ∨ (p5 ∨ p1))))) → False) ∨ (((p2 ∧ p2) ∨ False) → (False → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27713431927914329951894175552 : (((p2 ∨ p3) → (p1 → ((p3 ∨ (p5 ∨ (((p3 ∧ (p1 ∧ (((False ∨ p1) → (p1 ∨ p4)) ∨ p3))) → p4) ∨ (p1 ∧ p5)))) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693815810687846589998681503014 : ((((((p3 → (False ∧ (False ∧ (p1 → p4)))) ∧ ((p5 → p3) ∧ p2)) → p4) ∨ (((p1 → ((False ∧ p2) ∨ p2)) ∨ p4) ∨ (p5 → p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40320781761873752055746563556 : (((((True → (p5 ∧ (True ∧ ((((p3 ∨ (p4 ∧ (True → p3))) ∨ (p5 → (p1 ∧ (p3 → False)))) ∨ p3) ∨ p5)))) ∧ False) ∨ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185294785625735691119912620636 : ((p2 ∧ ((p2 → p3) ∨ (p3 → (p2 ∧ ((True ∧ p4) ∧ p4))))) ∨ ((p1 ∨ (True → (p2 → (p2 → (p4 → (False → p3)))))) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168873287638449289574688321039 : ((p4 ∨ (((p4 → True) ∨ (p4 ∧ ((p3 → p5) → False))) → ((p4 ∧ (p2 ∧ p2)) ∧ True))) → (p5 ∨ (p4 ∨ ((p5 → (p5 ∨ p3)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164906417239470163817287645673 : (((((p3 ∨ ((True ∨ p5) → p3)) ∧ (p4 ∨ ((p2 → (True ∨ p4)) → p1))) ∧ p3) → False) ∨ (p4 → (((p4 → True) → True) ∨ (False ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45280883704868323152099760742 : (((p2 ∧ (((False ∨ p1) → ((p5 → (p4 → (p3 ∧ (p1 ∧ ((p3 ∨ p2) ∧ p2))))) ∨ p5)) ∧ (p2 ∨ ((p1 ∨ p4) ∨ True)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37102487444471969398254432406 : (((((((((p5 → (p4 ∧ (False → p4))) → (p2 ∨ ((p5 ∧ (p3 → False)) ∧ (p4 ∨ p5)))) → False) ∨ p1) → p4) → p4) ∧ False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105483326763861695436664668386 : ((((p5 ∧ (p4 ∨ p3)) ∧ (((((p4 ∧ p5) ∧ p2) ∨ (False ∨ (p1 ∨ p4))) → p4) ∧ p2)) ∨ (False → ((p2 → p2) → p3))) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65358394098796046454425749718 : ((p3 ∨ (((p4 ∧ (p3 → p2)) ∨ ((True ∧ ((p5 ∧ (p4 → p3)) ∧ p1)) ∨ p3)) → (False ∨ (p1 ∨ ((True ∧ p4) → (p2 → p4)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106370409012495329887338809628 : ((((p1 ∨ (p1 ∨ (p5 ∧ (p1 → (p5 ∧ p1))))) ∨ p3) → ((True ∧ ((p4 ∧ (p5 ∨ True)) ∨ ((p3 ∨ p5) ∨ True))) ∨ p5)) ∧ (p2 → True)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167389866566606401045131551538 : ((((p4 → (p2 ∧ p2)) → (p2 ∧ ((p4 ∧ (p4 → (True → p4))) → (False ∧ False)))) → p2) → ((((p1 ∧ p4) ∧ True) → (p2 → p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172562010703574300446469358135 : (((p4 ∧ (p1 ∧ p1)) ∨ (((((p4 ∧ p1) → p5) ∧ (p5 ∧ p5)) → p1) ∨ p3)) ∨ (((p5 ∧ (p1 → p1)) ∨ ((p3 → True) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122099692312499779635210297028 : (((p5 → ((True → True) → (((True → (False ∧ p2)) ∨ (False → (True ∨ (p1 → ((p5 ∨ (p1 ∧ False)) ∧ p3))))) ∧ True))) → False) → (p3 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((True → True) → (((True → (False ∧ p2)) ∨ (False → (True ∨ (p1 → ((p5 ∨ (p1 ∧ False)) ∧ p3))))) ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 → ((True → True) → (((True → (False ∧ p2)) ∨ (False → (True ∨ (p1 → ((p5 ∨ (p1 ∧ False)) ∧ p3))))) ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111601333636295631825202540071 : ((((((((p2 ∨ (p1 ∨ (False ∨ p4))) ∧ p1) ∨ ((p3 ∨ ((True ∧ p4) ∧ (p4 ∨ p5))) → p3)) → False) ∧ p1) ∨ p2) ∨ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156883029770709465349703486742 : (((((p5 ∨ ((p4 → (p4 ∨ (((p4 → True) → (p1 ∧ True)) ∧ False))) → p3)) ∨ False) ∨ p4) ∨ False) ∨ (True ∧ (True → ((False ∧ False) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693949225874332200115568662318 : ((((((False ∨ (p1 ∧ ((p3 ∧ (True ∨ p5)) ∨ False))) ∧ p2) ∨ (True ∨ p2)) ∨ ((True ∨ (p5 ∧ (p3 ∧ ((False ∧ p5) ∧ p2)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255516823968725234926835636812 : ((p5 ∧ p2) → ((p5 ∧ p2) ∧ ((p3 ∧ ((p5 → (((True ∧ ((p1 → p2) → p1)) → p5) → (True ∧ p3))) ∨ p3)) ∨ ((p2 ∧ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38491559184729147304606913954 : ((((p5 → (((((p4 ∨ p1) → (False ∨ p1)) ∨ p4) → p5) → False)) ∧ ((((True ∧ ((p1 → p2) → p4)) → p4) ∨ p2) ∨ p1)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246219529335790582100382642194 : ((p4 ∧ p3) ∨ ((p4 ∨ ((p5 → p3) ∧ (p2 → p4))) ∨ ((((p4 ∧ (p4 ∧ (p3 → ((False ∧ p1) ∧ True)))) → p4) → True) → (p4 → True)))) := by
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
theorem thm_5_vars_124619759662186934472758965926 : (((True → (p3 ∨ (p1 ∧ (p4 ∧ p4)))) ∨ (p3 ∨ ((((p1 ∧ p5) → (p4 ∧ (p4 ∧ (p5 → p2)))) ∨ p3) ∨ (p1 → True)))) → (False ∨ True)) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1530857430647003322052034027 : (((False ∧ p2) ∧ (False ∧ (((p1 → (True ∧ ((p1 ∧ (p2 ∧ (((False ∨ True) ∧ p1) ∨ True))) ∧ False))) ∧ True) ∧ True))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327207442979883500674354635193 : (True → ((True → (((p1 ∨ (p3 ∧ ((p1 → p4) ∧ (p3 ∨ (p4 ∧ p3))))) ∨ (p3 ∨ (True ∨ p4))) ∧ (p1 → (p3 ∨ (True ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200731729500559680655353967210 : ((p3 ∧ ((p5 ∨ (p5 → (True ∨ p4))) → False)) → (((p2 ∨ False) ∨ (p3 → p1)) ∧ (False ∧ ((p1 ∧ (p2 → ((p3 → p1) ∧ p2))) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p5 → (True ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ (p5 → (True ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : (p5 ∨ (p5 → (True ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h19 := h16 h17
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117124384952215364382717833561 : (((p4 → False) → (p4 → (((((p5 ∧ p1) ∧ ((True ∨ ((p5 ∨ (False ∨ True)) ∨ p5)) → p1)) ∨ p4) ∨ p2) ∧ (p1 → p3)))) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307336009373120543500790661038 : (p1 ∨ (p3 ∨ ((p5 ∧ p3) ∨ ((((((p5 → p4) ∨ (True ∨ (p4 ∨ (p5 → (False ∧ p5))))) → p2) ∨ ((p3 ∧ p3) ∧ p1)) ∧ True) ∨ True)))) := by
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
theorem thm_5_vars_67651792814262849875511154795 : ((p1 → (p3 ∨ ((((p2 ∧ ((p3 ∧ (((True ∨ p5) ∧ (False ∨ p4)) ∨ False)) → (p4 ∧ True))) ∨ (p3 → p4)) ∧ (p4 ∧ True)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171405219410539606526938219263 : ((((((p5 → p3) ∨ p1) → p3) → (True ∧ (((True ∧ True) ∨ p5) → p2))) ∧ p4) ∨ ((p2 ∧ (True → p3)) ∨ ((True → (p2 ∨ False)) → p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187229398487878345667836305643 : (((p4 → p4) → ((p3 → (p5 ∨ (p4 → False))) ∨ (p4 → p3))) → ((p3 → (False ∨ p1)) ∨ (False → (p2 → (((True ∧ p1) → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165566502937068130216271406452 : (((((((p4 ∨ p2) → p4) → False) ∨ p4) ∨ True) ∨ ((p3 ∧ p4) ∨ ((p1 ∧ p4) ∧ True))) ∨ ((p1 ∨ (p2 ∨ True)) ∨ ((False ∨ p5) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157704586204651959153574654583 : (((((p5 ∧ p2) → (p5 → ((p3 → ((True → p5) ∨ False)) ∨ True))) → True) → (p4 ∧ (False ∨ p4))) ∨ ((True ∨ ((p1 ∨ p5) → p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38963128591249287814799867926 : ((((p5 → (p2 ∨ p4)) → (p4 → (((True → (p3 ∨ p3)) ∨ (p4 ∧ (((p2 ∨ True) ∧ p1) ∧ ((p4 → p1) ∧ p4)))) ∨ p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115297439300586978352099010496 : ((((True ∨ ((p4 ∧ p5) → ((p4 ∧ p2) ∧ p4))) ∨ True) → (((True ∨ True) ∧ ((True ∧ (p3 ∧ (True ∨ p5))) ∨ p1)) ∧ p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110865666791824282545587202676 : (((((((p3 → ((False ∨ (((p5 → p5) ∧ (p2 ∧ False)) ∨ True)) → p5)) → ((p4 ∧ p2) ∨ p5)) ∨ True) → True) → p3) ∧ p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50094451422118436584675726792 : (((p3 ∧ ((p2 ∧ (((p4 → p2) → p3) ∧ (((p3 ∨ (False → p1)) → True) ∨ True))) ∧ (p4 ∨ p1))) ∧ (((True ∨ p2) → p3) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706546580250718354035049892598 : ((((True → (True → (p2 ∧ (p2 ∨ (p4 ∧ p2))))) ∧ (p5 ∧ (p1 → (False ∧ (p2 ∧ (p4 ∧ (((p3 ∨ (True → p4)) ∨ False) ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603532500540087279387917945359 : ((((p3 ∨ (((p4 ∧ p3) ∧ True) → ((((True → p1) ∧ p4) ∨ True) ∧ ((True ∨ (p2 → p1)) ∧ (((p1 ∨ p4) → False) ∨ True))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677745529964150186417382975485 : (((((p2 ∧ ((((((p1 → p2) ∧ (True → p4)) → (p2 ∨ False)) ∨ p5) ∨ p5) → (p4 ∨ p1))) → p4) ∨ (((p1 ∧ p1) ∧ False) → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661995405797582401055127567405 : ((((((p3 ∧ (((p3 ∧ (p4 ∨ p5)) ∨ (p5 ∧ (p4 ∨ p1))) → True)) → p2) → ((p5 ∧ ((p2 → p3) ∧ p4)) ∧ p3)) → (p2 → p5)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ (((p3 ∧ (p4 ∨ p5)) ∨ (p5 ∧ (p4 ∨ p1))) → True)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647244387336409849207989668215 : ((((p4 → ((p2 ∧ ((p1 → (p4 → (p1 ∨ (p1 ∨ p3)))) ∨ (p1 → (p3 ∧ (p5 ∨ ((p4 ∧ False) → (p2 ∨ p1))))))) ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734415763736966953782924493241 : ((((False ∨ p5) ∧ ((p2 ∨ ((((p5 ∨ True) ∨ (True ∧ p3)) ∧ ((False → False) → (True ∨ (p3 ∧ (False → p5))))) ∨ (False ∧ p2))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265015422389483975163062396652 : (True ∧ ((p5 → p1) → (((((False → p4) → False) ∨ ((p2 ∨ (p4 → ((((p2 ∨ p2) → (False ∧ p1)) → p4) ∧ True))) → True)) ∨ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632111020026812430822213370609 : ((((((False ∨ p4) ∨ (((((((p4 → p5) ∨ p4) → p5) → p3) → ((p3 → p4) ∨ p1)) ∧ ((p5 ∨ p2) → True)) ∧ p2)) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134967519817663398961648434007 : (((((p1 ∨ ((p2 → p3) ∨ p1)) ∧ p5) ∨ ((p3 ∧ ((p5 ∨ p5) ∨ ((p3 ∧ p3) ∨ p4))) ∨ p4)) ∧ (p1 ∨ p2)) ∨ ((p2 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96333887222772738452591405751 : ((False ∨ (((p4 ∨ (p4 ∧ ((p3 → ((True → True) ∧ False)) ∧ (p4 → (((p3 ∨ (False ∨ p2)) ∨ False) ∧ p4))))) ∨ (True ∨ p5)) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∨ (p4 ∧ ((p3 → ((True → True) ∧ False)) ∧ (p4 → (((p3 ∨ (False ∨ p2)) ∨ False) ∧ p4))))) ∨ (True ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138203883961194170903857366340 : ((p1 → (p4 → ((True ∨ False) → ((((((p2 → p2) ∧ p3) ∨ p2) → False) ∧ (True ∨ (p3 ∨ p4))) → (p2 ∧ p1))))) ∨ (True ∨ (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14446185244099561203012355545 : (((((((p4 ∨ p3) ∨ (p1 ∧ (((p3 → p5) ∨ (p1 ∨ (True ∨ (True → p1)))) ∧ (True ∧ p4)))) ∧ p2) ∨ p3) ∧ p3) ∨ (False ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256034342953354923630629090141 : ((True ∨ p4) → ((p4 ∨ ((((((p3 ∨ True) ∨ (p1 ∧ p2)) → p4) ∨ True) ∧ (True ∧ (((p4 ∨ (p4 ∨ p4)) ∧ False) → p3))) ∧ p2)) ∨ True)) := by
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
theorem thm_5_vars_355844863563728868209543304317 : (p5 → ((((p1 ∧ True) ∨ (p1 ∨ (p1 ∨ (p3 → (((True ∨ (p2 ∧ True)) ∧ (p4 ∨ True)) ∧ (p5 ∨ False)))))) → p4) ∨ ((p5 ∧ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117846152364735509243992649748 : ((p4 ∧ (p2 → (((((p2 → p2) ∨ (p2 → p5)) ∧ (((p1 ∧ True) → p1) ∨ (False → False))) ∧ p1) → ((p2 ∧ p4) ∨ p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64986179661684215819265418503 : ((p2 ∨ ((p4 → ((p3 → p2) ∧ p1)) → (((((p3 ∨ p4) ∧ ((p2 ∧ (p5 → p4)) → p1)) → p2) ∨ (p1 → p3)) ∨ (p2 ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811340686114948839692724392560 : (((p5 → (False ∨ (p3 → ((p5 ∧ p1) ∨ ((p3 ∨ False) → ((p3 ∧ ((p4 → (p1 → ((True ∧ p3) ∨ (p4 ∨ False)))) → p1)) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164729197274934192865141373105 : ((((p3 ∧ ((((p3 → ((p3 ∧ True) → False)) → (p5 ∨ False)) → p3) ∧ p5)) → p4) ∨ p3) ∨ ((((p2 ∨ p3) ∨ (False ∨ p3)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102904171227408202084992969921 : ((((p4 → ((((((p4 ∧ (p4 ∧ p4)) ∧ p3) ∧ p3) → ((False ∧ p1) ∨ True)) ∧ p5) ∨ p3)) ∧ (p3 ∨ (False ∧ True))) ∨ True) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200720833556348543195604323634 : ((p3 ∧ (((p4 ∧ p2) ∧ (p3 → p2)) ∧ p1)) → ((p1 → (p5 → p5)) ∧ (((p5 ∧ (False ∨ (p3 → ((p4 ∧ p2) → p5)))) ∧ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136236191193176710250894696074 : ((((p3 ∨ p2) ∧ ((p3 ∧ p4) ∧ True)) ∨ (False ∨ ((p2 → (((True ∧ False) ∨ p1) → (p3 → (True → p3)))) ∨ False))) ∨ (p5 ∨ (p5 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46923284075904259025630583918 : (((((False ∨ (True ∨ p5)) ∧ ((False ∨ ((p1 ∧ p3) ∧ (False ∧ (p5 → ((False ∨ p3) ∨ (p4 ∨ p2)))))) ∨ True)) ∨ p3) ∨ (p2 ∧ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324301711537857771427241027228 : (p5 ∨ (((p2 → p2) ∨ ((p5 ∨ False) ∧ (p4 ∨ p3))) → ((((((p2 → p5) → (p3 ∨ True)) ∨ p1) ∧ p4) ∨ p3) ∨ (True ∨ (p5 → p4))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
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
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316473882015560747873738596771 : (p3 ∨ (p1 ∨ (p5 ∨ ((p2 ∨ (((((p3 → p1) → p1) ∨ False) ∨ False) → (((p1 ∨ (((p1 ∧ p3) → p1) ∧ p2)) → p4) → p1))) ∨ True)))) := by
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
theorem thm_5_vars_261332250543451179745266063073 : ((p5 → False) → ((((False ∨ p1) ∨ (((((p3 → True) ∨ p5) ∨ False) → (p3 ∨ p3)) ∨ (False → True))) ∨ p2) ∨ ((p4 → (True ∧ p4)) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



